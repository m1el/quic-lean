// gquiche_shim.cc -- Google QUICHE behind the C interface of gquiche_shim.h.
//
// What is put together here, and why it needs no patch to QUICHE:
//
//   crypto   QuicEncrypter / QuicDecrypter are interfaces, so the stub cipher
//            of conn_driver.h and Quic.Protection.stub (payload in the clear,
//            tag = 16 x 0xA5, header-protection mask = first five bytes of the
//            sample) is installed directly.  Packets need no conversion.
//   keys     A QuicCryptoStream that performs no handshake: keys are installed
//            by hand, the peer's transport parameters are handed to QuicConfig,
//            and OnTlsHandshakeComplete() is called -- what
//            quic_session_test.cc's TestCryptoStream does.  Initial and
//            Handshake keys are dropped at the end of setup, so such packets
//            are undecryptable, as they are to ngtcp2 after
//            ngtcp2_conn_discard_*_state.
//   clock    QuicConnectionHelperInterface supplies the clock and
//            QuicAlarmFactory the alarms; both are ours.  An alarm only fires
//            from gq_fire_alarms.
//   output   QuicPacketWriter is ours and queues datagrams for gq_pop_out.
//   random   QuicRandom is ours and deterministic.

#include "gquiche_shim.h"

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <deque>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>

#include "absl/log/globals.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "quiche/quic/core/crypto/crypto_message_parser.h"
#include "quiche/quic/core/crypto/quic_decrypter.h"
#include "quiche/quic/core/crypto/quic_encrypter.h"
#include "quiche/quic/core/crypto/quic_random.h"
#include "quiche/quic/core/crypto/transport_parameters.h"
#include "quiche/quic/core/deterministic_connection_id_generator.h"
#include "quiche/quic/core/quic_alarm.h"
#include "quiche/quic/core/quic_alarm_factory.h"
#include "quiche/quic/core/quic_clock.h"
#include "quiche/quic/core/quic_config.h"
#include "quiche/quic/core/quic_connection.h"
#include "quiche/quic/core/quic_crypto_stream.h"
#include "quiche/quic/core/quic_packet_writer.h"
#include "quiche/quic/core/quic_session.h"
#include "quiche/quic/core/quic_stream.h"
#include "quiche/quic/core/quic_utils.h"
#include "quiche/quic/core/quic_versions.h"
#include "quiche/common/simple_buffer_allocator.h"

namespace {

using namespace quic;  // NOLINT

constexpr size_t kTagLen = 16;
// QuicTime::Zero() means "not set" throughout QUICHE, so the harness's ts = 0
// must not be it.
constexpr int64_t kClockBaseUs = 3600ll * 1000 * 1000;

// ------------------------------------------------------------ stub cipher

class StubEncrypter : public QuicEncrypter {
 public:
  bool SetKey(absl::string_view) override { return true; }
  bool SetNoncePrefix(absl::string_view) override { return true; }
  bool SetIV(absl::string_view) override { return true; }
  bool SetHeaderProtectionKey(absl::string_view) override { return true; }
  size_t GetKeySize() const override { return 16; }
  size_t GetIVSize() const override { return 12; }
  size_t GetNoncePrefixSize() const override { return 4; }
  bool EncryptPacket(uint64_t, absl::string_view, absl::string_view plaintext,
                     char* output, size_t* output_length,
                     size_t max_output_length) override {
    if (max_output_length < plaintext.size() + kTagLen) return false;
    memmove(output, plaintext.data(), plaintext.size());
    memset(output + plaintext.size(), 0xa5, kTagLen);
    *output_length = plaintext.size() + kTagLen;
    return true;
  }
  std::string GenerateHeaderProtectionMask(absl::string_view sample) override {
    if (sample.size() < 5) return std::string();
    return std::string(sample.substr(0, 5));
  }
  size_t GetMaxPlaintextSize(size_t ciphertext_size) const override {
    return ciphertext_size - std::min(ciphertext_size, kTagLen);
  }
  size_t GetCiphertextSize(size_t plaintext_size) const override {
    return plaintext_size + kTagLen;
  }
  QuicPacketCount GetConfidentialityLimit() const override {
    return std::numeric_limits<QuicPacketCount>::max();
  }
  absl::string_view GetKey() const override { return absl::string_view(); }
  absl::string_view GetNoncePrefix() const override {
    return absl::string_view();
  }
};

class StubDecrypter : public QuicDecrypter {
 public:
  bool SetKey(absl::string_view) override { return true; }
  bool SetNoncePrefix(absl::string_view) override { return true; }
  bool SetIV(absl::string_view) override { return true; }
  bool SetHeaderProtectionKey(absl::string_view) override { return true; }
  bool SetPreliminaryKey(absl::string_view) override { return false; }
  bool SetDiversificationNonce(const DiversificationNonce&) override {
    return false;
  }
  size_t GetKeySize() const override { return 16; }
  size_t GetIVSize() const override { return 12; }
  size_t GetNoncePrefixSize() const override { return 4; }
  bool DecryptPacket(uint64_t, absl::string_view, absl::string_view ciphertext,
                     char* output, size_t* output_length,
                     size_t max_output_length) override {
    if (ciphertext.size() < kTagLen) return false;
    size_t n = ciphertext.size() - kTagLen;
    if (n > max_output_length) return false;
    memmove(output, ciphertext.data(), n);
    *output_length = n;
    return true;
  }
  std::string GenerateHeaderProtectionMask(
      QuicDataReader* sample_reader) override {
    absl::string_view sample;
    if (!sample_reader->ReadStringPiece(&sample, 16)) return std::string();
    return std::string(sample.substr(0, 5));
  }
  uint32_t cipher_id() const override { return 0; }
  QuicPacketCount GetIntegrityLimit() const override {
    return std::numeric_limits<QuicPacketCount>::max();
  }
  absl::string_view GetKey() const override { return absl::string_view(); }
  absl::string_view GetNoncePrefix() const override {
    return absl::string_view();
  }
};

// ------------------------------------------------- clock, alarms, random

class ShimClock : public QuicClock {
 public:
  void Set(uint64_t ns) { us_ = kClockBaseUs + static_cast<int64_t>(ns / 1000); }
  QuicTime Now() const override {
    return QuicTime::Zero() + QuicTime::Delta::FromMicroseconds(us_);
  }
  QuicTime ApproximateNow() const override { return Now(); }
  QuicWallTime WallNow() const override {
    return QuicWallTime::FromUNIXMicroseconds(us_);
  }

 private:
  int64_t us_ = kClockBaseUs;
};

class ShimAlarmFactory;

class ShimAlarm : public QuicAlarm {
 public:
  ShimAlarm(ShimAlarmFactory* factory,
            QuicArenaScopedPtr<QuicAlarm::Delegate> delegate);
  ~ShimAlarm() override;
  void SetImpl() override {}
  void CancelImpl() override {}
  using QuicAlarm::Fire;
  uint64_t serial() const { return serial_; }

 private:
  ShimAlarmFactory* factory_;
  uint64_t serial_;
};

class ShimAlarmFactory : public QuicAlarmFactory {
 public:
  QuicAlarm* CreateAlarm(QuicAlarm::Delegate* delegate) override {
    return new ShimAlarm(this, QuicArenaScopedPtr<QuicAlarm::Delegate>(delegate));
  }
  QuicArenaScopedPtr<QuicAlarm> CreateAlarm(
      QuicArenaScopedPtr<QuicAlarm::Delegate> delegate,
      QuicConnectionArena* arena) override {
    if (arena != nullptr)
      return arena->New<ShimAlarm>(this, std::move(delegate));
    return QuicArenaScopedPtr<QuicAlarm>(new ShimAlarm(this, std::move(delegate)));
  }

  // The set alarm with the earliest deadline; creation order breaks ties, so
  // that a run does not depend on where the allocator put the alarms.
  ShimAlarm* Earliest() const {
    ShimAlarm* best = nullptr;
    for (ShimAlarm* a : alarms_) {
      if (!a->IsSet()) continue;
      if (best == nullptr || a->deadline() < best->deadline() ||
          (a->deadline() == best->deadline() && a->serial() < best->serial()))
        best = a;
    }
    return best;
  }

  std::set<ShimAlarm*> alarms_;
  uint64_t next_serial_ = 0;
};

ShimAlarm::ShimAlarm(ShimAlarmFactory* factory,
                     QuicArenaScopedPtr<QuicAlarm::Delegate> delegate)
    : QuicAlarm(std::move(delegate)),
      factory_(factory),
      serial_(factory->next_serial_++) {
  factory_->alarms_.insert(this);
}
ShimAlarm::~ShimAlarm() { factory_->alarms_.erase(this); }

class ShimRandom : public QuicRandom {
 public:
  void RandBytes(void* data, size_t len) override {
    uint8_t* p = static_cast<uint8_t*>(data);
    for (size_t i = 0; i < len; ++i) p[i] = static_cast<uint8_t>(Next() >> 24);
  }
  uint64_t RandUint64() override { return (Next() << 32) ^ Next(); }
  void InsecureRandBytes(void* data, size_t len) override { RandBytes(data, len); }
  uint64_t InsecureRandUint64() override { return RandUint64(); }

 private:
  uint64_t Next() {
    state_ = state_ * 6364136223846793005ull + 1442695040888963407ull;
    return state_ >> 16;
  }
  uint64_t state_ = 0x12345678u;
};

class ShimHelper : public QuicConnectionHelperInterface {
 public:
  const QuicClock* GetClock() const override { return &clock; }
  QuicRandom* GetRandomGenerator() override { return &random; }
  quiche::QuicheBufferAllocator* GetStreamSendBufferAllocator() override {
    return &allocator;
  }
  ShimClock clock;
  ShimRandom random;
  quiche::SimpleBufferAllocator allocator;
};

// ---------------------------------------------------------------- writer

class ShimWriter : public QuicPacketWriter {
 public:
  WriteResult WritePacket(const char* buffer, size_t buf_len,
                          const QuicIpAddress&, const QuicSocketAddress&,
                          PerPacketOptions*,
                          const QuicPacketWriterParams&) override {
    out.emplace_back(std::string(buffer, buf_len), DcidLen());
    return WriteResult(WRITE_STATUS_OK, static_cast<int>(buf_len));
  }
  bool IsWriteBlocked() const override { return false; }
  void SetWritable() override {}
  std::optional<int> MessageTooBigErrorCode() const override {
    return std::nullopt;
  }
  QuicByteCount GetMaxPacketSize(const QuicSocketAddress&) const override {
    return kMaxOutgoingPacketSize;
  }
  bool SupportsReleaseTime() const override { return false; }
  bool IsBatchMode() const override { return false; }
  bool SupportsEcn() const override { return false; }
  QuicPacketBuffer GetNextWriteLocation(const QuicIpAddress&,
                                        const QuicSocketAddress&) override {
    return {nullptr, nullptr};
  }
  WriteResult Flush() override { return WriteResult(WRITE_STATUS_OK, 0); }

  // The length of the connection ID we address the peer with, which a short
  // header does not carry.  Noted per datagram: it changes between writes when
  // the peer retires the connection ID in use.
  size_t DcidLen() const {
    if (connection == nullptr) return 0;
    return connection->perspective() == Perspective::IS_SERVER
               ? connection->client_connection_id().length()
               : connection->connection_id().length();
  }

  QuicConnection* connection = nullptr;
  std::deque<std::pair<std::string, size_t>> out;
};

// ------------------------------------------------- crypto stream, streams

using EventQueue = std::deque<std::string>;

class AcceptAllParser : public CryptoMessageParser {
 public:
  explicit AcceptAllParser(EventQueue* events) : events_(events) {}
  QuicErrorCode error() const override { return QUIC_NO_ERROR; }
  const std::string& error_detail() const override { return detail_; }
  bool ProcessInput(absl::string_view input, EncryptionLevel) override {
    events_->push_back(absl::StrFormat("recv_crypto_data level=1rtt off=%u len=%u",
                                       static_cast<unsigned>(offset_),
                                       static_cast<unsigned>(input.size())));
    offset_ += input.size();
    return true;
  }
  size_t InputBytesRemaining() const override { return 0; }

 private:
  EventQueue* events_;
  std::string detail_;
  uint64_t offset_ = 0;
};

class ShimCryptoStream : public QuicCryptoStream {
 public:
  ShimCryptoStream(QuicSession* session, EventQueue* events)
      : QuicCryptoStream(session),
        parser_(events),
        params_(new QuicCryptoNegotiatedParameters) {
    params_->cipher_suite = 1;  // any non-zero value: "negotiated"
  }

  void set_complete() { complete_ = true; }

  bool ExportKeyingMaterial(absl::string_view, absl::string_view, size_t,
                            std::string*) override {
    return false;
  }
  ssl_early_data_reason_t EarlyDataReason() const override {
    return ssl_early_data_unknown;
  }
  bool encryption_established() const override { return complete_; }
  bool one_rtt_keys_available() const override { return complete_; }
  const QuicCryptoNegotiatedParameters& crypto_negotiated_params()
      const override {
    return *params_;
  }
  CryptoMessageParser* crypto_message_parser() override { return &parser_; }
  void OnPacketDecrypted(EncryptionLevel) override {}
  void OnOneRttPacketAcknowledged() override {}
  void OnHandshakePacketSent() override {}
  void OnHandshakeDoneReceived() override {}
  void OnNewTokenReceived(absl::string_view) override {}
  std::string GetAddressToken(const CachedNetworkParameters*) const override {
    return "";
  }
  bool ValidateAddressToken(absl::string_view) const override { return true; }
  const CachedNetworkParameters* PreviousCachedNetworkParams() const override {
    return nullptr;
  }
  void SetPreviousCachedNetworkParams(CachedNetworkParameters) override {}
  HandshakeState GetHandshakeState() const override {
    return complete_ ? HANDSHAKE_CONFIRMED : HANDSHAKE_START;
  }
  void SetServerApplicationStateForResumption(
      std::unique_ptr<ApplicationState>) override {}
  std::unique_ptr<QuicDecrypter> AdvanceKeysAndCreateCurrentOneRttDecrypter()
      override {
    return std::make_unique<StubDecrypter>();
  }
  std::unique_ptr<QuicEncrypter> CreateCurrentOneRttEncrypter() override {
    return std::make_unique<StubEncrypter>();
  }
  SSL* GetSsl() const override { return nullptr; }
  bool IsCryptoFrameExpectedForEncryptionLevel(
      EncryptionLevel level) const override {
    return level != ENCRYPTION_ZERO_RTT;
  }
  EncryptionLevel GetEncryptionLevelToSendCryptoDataOfSpace(
      PacketNumberSpace space) const override {
    switch (space) {
      case INITIAL_DATA: return ENCRYPTION_INITIAL;
      case HANDSHAKE_DATA: return ENCRYPTION_HANDSHAKE;
      default: return ENCRYPTION_FORWARD_SECURE;
    }
  }

 private:
  AcceptAllParser parser_;
  quiche::QuicheReferenceCountedPointer<QuicCryptoNegotiatedParameters> params_;
  bool complete_ = false;
};

class ShimStream : public QuicStream {
 public:
  ShimStream(QuicStreamId id, QuicSession* session, StreamType type,
             EventQueue* events)
      : QuicStream(id, session, /*is_static=*/false, type), events_(events) {}

  // The application of conn_driver.h reads everything at once.
  void OnDataAvailable() override {
    char sink[4096];
    uint64_t off = sequencer()->NumBytesConsumed();
    size_t total = 0;
    for (;;) {
      struct iovec iov = {sink, sizeof(sink)};
      size_t n = sequencer()->Readv(&iov, 1);
      if (n == 0) break;
      total += n;
    }
    bool fin = sequencer()->IsClosed();
    if (total != 0 || fin)
      events_->push_back(absl::StrFormat(
          "recv_stream_data id=%u off=%u len=%u fin=%d early=0",
          static_cast<unsigned>(id()), static_cast<unsigned>(off),
          static_cast<unsigned>(total), fin ? 1 : 0));
    if (fin) OnFinRead();
  }

  // Once per stream, as ngtcp2's callbacks are: QUICHE calls these for every
  // frame, duplicates included.
  void OnStreamReset(const QuicRstStreamFrame& frame) override {
    if (!reset_seen_) events_->push_back(absl::StrFormat(
        "stream_reset id=%u final_size=%u app_error_code=%u",
        static_cast<unsigned>(id()), static_cast<unsigned>(frame.byte_offset),
        static_cast<unsigned>(frame.ietf_error_code)));
    reset_seen_ = true;
    QuicStream::OnStreamReset(frame);
  }

  bool OnStopSending(QuicResetStreamError error) override {
    if (!stop_seen_) events_->push_back(absl::StrFormat(
        "recv_stop_sending id=%u app_error_code=%u",
        static_cast<unsigned>(id()), static_cast<unsigned>(error.ietf_application_code())));
    stop_seen_ = true;
    return QuicStream::OnStopSending(error);
  }

 private:
  EventQueue* events_;
  bool reset_seen_ = false;
  bool stop_seen_ = false;
};

class ShimSession : public QuicSession {
 public:
  ShimSession(QuicConnection* connection, const QuicConfig& config,
              EventQueue* events)
      : QuicSession(connection, /*owner=*/nullptr, config,
                    connection->supported_versions(),
                    /*num_expected_unidirectional_static_streams=*/0),
        events_(events),
        crypto_(this, events) {}

  ~ShimSession() override { DeleteConnection(); }

  ShimCryptoStream* crypto() { return &crypto_; }
  QuicCryptoStream* GetMutableCryptoStream() override { return &crypto_; }
  const QuicCryptoStream* GetCryptoStream() const override { return &crypto_; }

  QuicStream* CreateIncomingStream(QuicStreamId id) override {
    StreamType type = QuicUtils::GetStreamType(
        id, perspective(), /*peer_initiated=*/true, version());
    auto* s = new ShimStream(id, this, type, events_);
    events_->push_back(absl::StrFormat("stream_open id=%u", static_cast<unsigned>(id)));
    ActivateStream(std::unique_ptr<QuicStream>(s));
    return s;
  }
  bool ShouldKeepConnectionAlive() const override { return false; }

  int64_t Open(bool uni) {
    if (uni ? !CanOpenNextOutgoingUnidirectionalStream()
            : !CanOpenNextOutgoingBidirectionalStream())
      return -1;
    QuicStreamId id = uni ? GetNextOutgoingUnidirectionalStreamId()
                          : GetNextOutgoingBidirectionalStreamId();
    ActivateStream(std::make_unique<ShimStream>(
        id, this, uni ? WRITE_UNIDIRECTIONAL : BIDIRECTIONAL, events_));
    return static_cast<int64_t>(id);
  }

  QuicStream* Find(int64_t sid) {
    if (sid < 0) return nullptr;
    return GetActiveStream(static_cast<QuicStreamId>(sid));
  }

  void OnConnectionClosed(const QuicConnectionCloseFrame& frame,
                          ConnectionCloseSource source) override {
    if (status == 0) {
      detail = absl::StrFormat("%s: %s", QuicErrorCodeToString(frame.quic_error_code),
                               frame.error_details);
      if (source == ConnectionCloseSource::FROM_SELF &&
          frame.close_type == IETF_QUIC_TRANSPORT_CONNECTION_CLOSE &&
          frame.wire_error_code != 0 &&
          frame.quic_error_code != QUIC_NETWORK_IDLE_TIMEOUT &&
          frame.quic_error_code != QUIC_HANDSHAKE_TIMEOUT)
        status = 1 + static_cast<int>(frame.wire_error_code);
      else
        status = -1;
    }
    QuicSession::OnConnectionClosed(frame, source);
  }

  int status = 0;
  std::string detail;

 private:
  EventQueue* events_;
  ShimCryptoStream crypto_;
};

}  // namespace

struct gq_conn {
  explicit gq_conn(uint8_t cidlen) : generator(cidlen) {}

  ShimHelper helper;
  ShimAlarmFactory alarms;
  ShimWriter writer;
  DeterministicConnectionIdGenerator generator;
  EventQueue events;
  QuicSocketAddress self, peer;
  QuicConnection* connection = nullptr;  // owned by |session|
  std::unique_ptr<ShimSession> session;
};

extern "C" {

gq_conn* gq_new(int server, const uint8_t* local_cid, const uint8_t* remote_cid,
                size_t cidlen, uint64_t now) {
  static bool once;
  if (!once) {
    once = true;
    if (getenv("GQ_DEBUG") == nullptr) {
      absl::SetStderrThreshold(absl::LogSeverityAtLeast::kFatal);
      absl::SetMinLogLevel(absl::LogSeverityAtLeast::kFatal);
    }
  }

  auto* g = new gq_conn(static_cast<uint8_t>(cidlen));
  g->helper.clock.Set(now);
  // conn_driver.h's addresses: we are 127.0.0.1:4433, the peer :12345.
  g->self = QuicSocketAddress(QuicIpAddress::Loopback4(), 4433);
  g->peer = QuicSocketAddress(QuicIpAddress::Loopback4(), 12345);

  QuicConnectionId local(reinterpret_cast<const char*>(local_cid), cidlen);
  QuicConnectionId remote(reinterpret_cast<const char*>(remote_cid), cidlen);
  const QuicConnectionId& server_cid = server ? local : remote;
  const QuicConnectionId& client_cid = server ? remote : local;
  Perspective perspective = server ? Perspective::IS_SERVER : Perspective::IS_CLIENT;
  ParsedQuicVersionVector versions = {ParsedQuicVersion::RFCv1()};

  g->connection = new QuicConnection(server_cid, g->self, g->peer, &g->helper,
                                     &g->alarms, &g->writer,
                                     /*owns_writer=*/false, perspective,
                                     versions, g->generator);
  g->connection->set_client_connection_id(client_cid);
  g->writer.connection = g->connection;
  g->connection->SetMaxPacketLength(1200);

  // conn_driver.h's fill_params, item for item -- what we advertise ...
  QuicConfig config;
  config.SetIdleNetworkTimeout(QuicTime::Delta::FromSeconds(30));
  config.SetMaxBidirectionalStreamsToSend(4);
  config.SetMaxUnidirectionalStreamsToSend(2);
  config.SetInitialMaxStreamDataBytesIncomingBidirectionalToSend(1024);
  config.SetInitialMaxStreamDataBytesOutgoingBidirectionalToSend(1024);
  config.SetInitialMaxStreamDataBytesUnidirectionalToSend(1024);
  config.SetMaxAckDelayToSendMs(25);
  config.SetAckDelayExponentToSend(3);
  config.SetActiveConnectionIdLimitToSend(4);
  config.SetMaxDatagramFrameSizeToSend(1200);

  g->session = std::make_unique<ShimSession>(g->connection, config, &g->events);
  g->session->Initialize();
  // QuicConfig refuses a connection window below 16 KiB
  // (kMinimumFlowControlSendWindow); the flow controller itself does not.
  g->session->flow_controller()->UpdateReceiveWindowSize(4096);

  // Handshake and 1-RTT keys.  The encrypter first: QuicSession refuses a
  // decrypter for a space it cannot yet acknowledge in.
  for (EncryptionLevel level : {ENCRYPTION_HANDSHAKE, ENCRYPTION_FORWARD_SECURE}) {
    g->session->OnNewEncryptionKeyAvailable(level,
                                            std::make_unique<StubEncrypter>());
    if (!g->session->OnNewDecryptionKeyAvailable(
            level, std::make_unique<StubDecrypter>(),
            /*set_alternative_decrypter=*/false, /*latch_once_used=*/false)) {
      fprintf(stderr, "gquiche_shim: decrypter refused\n");
      gq_free(g);
      return nullptr;
    }
  }

  // ... and what the peer advertised: the same.
  TransportParameters tp;
  tp.perspective = server ? Perspective::IS_CLIENT : Perspective::IS_SERVER;
  tp.max_idle_timeout_ms.set_value(30000);
  tp.max_udp_payload_size.set_value(65527);
  tp.initial_max_data.set_value(4096);
  tp.initial_max_stream_data_bidi_local.set_value(1024);
  tp.initial_max_stream_data_bidi_remote.set_value(1024);
  tp.initial_max_stream_data_uni.set_value(1024);
  tp.initial_max_streams_bidi.set_value(4);
  tp.initial_max_streams_uni.set_value(2);
  tp.ack_delay_exponent.set_value(3);
  tp.max_ack_delay.set_value(25);
  tp.active_connection_id_limit.set_value(4);
  tp.max_datagram_frame_size.set_value(1200);
  tp.initial_source_connection_id = remote;
  if (!server) tp.original_destination_connection_id = remote;
  std::string error;
  if (g->session->config()->ProcessTransportParameters(
          tp, /*is_resumption=*/false, &error) != QUIC_NO_ERROR) {
    fprintf(stderr, "gquiche_shim: transport parameters: %s\n", error.c_str());
    gq_free(g);
    return nullptr;
  }
  g->session->OnConfigNegotiated();
  return g;
}

int gq_handshake_done(gq_conn* g) {
  const bool server = g->connection->perspective() == Perspective::IS_SERVER;
  g->session->crypto()->set_complete();
  g->session->OnTlsHandshakeComplete();
  // What TlsServerHandshaker / TlsClientHandshaker do next.  Dropping the
  // Handshake keys is what tells QuicConnection the handshake is over
  // (NeuterHandshakeData -> OnHandshakeComplete).  The Initial keys are real
  // ones, installed by QuicConnection's constructor, and a closing connection
  // would write its CONNECTION_CLOSE under them as well.
  g->session->DiscardOldEncryptionKey(ENCRYPTION_INITIAL);
  g->session->DiscardOldDecryptionKey(ENCRYPTION_INITIAL);
  if (!server) g->session->OnTlsHandshakeConfirmed();
  g->session->DiscardOldEncryptionKey(ENCRYPTION_HANDSHAKE);
  g->session->DiscardOldDecryptionKey(ENCRYPTION_HANDSHAKE);
  if (!g->connection->connected()) {
    fprintf(stderr, "gquiche_shim: closed during setup: %s\n",
            g->session->detail.c_str());
    return -1;
  }
  return 0;
}

void gq_free(gq_conn* g) {
  if (g == nullptr) return;
  g->writer.connection = nullptr;  // the session's destructor may still write
  g->session.reset();
  delete g;
}

void gq_set_clock(gq_conn* g, uint64_t now) { g->helper.clock.Set(now); }

void gq_recv(gq_conn* g, const uint8_t* buf, size_t len) {
  QuicReceivedPacket packet(reinterpret_cast<const char*>(buf), len,
                            g->helper.clock.Now());
  g->connection->ProcessUdpPacket(g->self, g->peer, packet);
  if (getenv("GQ_DEBUG") != nullptr) {
    const QuicConnectionStats& st = g->connection->GetStats();
    fprintf(stderr,
            "gq: recv len=%zu received=%llu processed=%llu dropped=%llu "
            "undecryptable=%llu connected=%d level=%d framer=\"%s\" "
            "can_write=%d ack_alarm=%d amp_throttled=%llu\n",
            len, (unsigned long long)st.packets_received,
            (unsigned long long)st.packets_processed,
            (unsigned long long)st.packets_dropped,
            (unsigned long long)st.undecryptable_packets_received_before_handshake_complete,
            g->connection->connected(), (int)g->connection->encryption_level(),
            const_cast<QuicFramer&>(g->connection->framer()).detailed_error().c_str(),
            g->connection->connected() && g->connection->CanWrite(NO_RETRANSMITTABLE_DATA),
            g->connection->connected() && g->connection->HasPendingAcks(),
            (unsigned long long)st.num_amplification_throttling);
  }
}

void gq_fire_alarms(gq_conn* g) {
  QuicTime now = g->helper.clock.Now();
  for (int guard = 0; guard < 64; ++guard) {
    ShimAlarm* a = g->alarms.Earliest();
    if (a == nullptr || a->deadline() > now) break;
    a->Fire();
  }
}

uint64_t gq_next_deadline(gq_conn* g) {
  ShimAlarm* a = g->alarms.Earliest();
  if (a == nullptr) return UINT64_MAX;
  int64_t us = (a->deadline() - QuicTime::Zero()).ToMicroseconds() - kClockBaseUs;
  return us < 0 ? 0 : static_cast<uint64_t>(us) * 1000;
}

void gq_can_write(gq_conn* g) {
  if (g->connection->connected()) g->connection->OnCanWrite();
}

size_t gq_pop_out(gq_conn* g, uint8_t* buf, size_t cap, size_t* dcidlen) {
  while (!g->writer.out.empty()) {
    std::string d = std::move(g->writer.out.front().first);
    *dcidlen = g->writer.out.front().second;
    g->writer.out.pop_front();
    if (d.empty() || d.size() > cap) continue;
    memcpy(buf, d.data(), d.size());
    return d.size();
  }
  return 0;
}

size_t gq_pop_event(gq_conn* g, char* buf, size_t cap) {
  if (g->events.empty() || cap == 0) return 0;
  std::string e = std::move(g->events.front());
  g->events.pop_front();
  size_t n = std::min(e.size(), cap - 1);
  memcpy(buf, e.data(), n);
  buf[n] = 0;
  return n;
}

int gq_status(gq_conn* g) { return g->session->status; }
const char* gq_close_detail(gq_conn* g) { return g->session->detail.c_str(); }

int64_t gq_open(gq_conn* g, int uni) {
  if (!g->connection->connected()) return -1;
  return g->session->Open(uni != 0);
}

int gq_write(gq_conn* g, int64_t sid, const uint8_t* data, size_t n, int fin) {
  if (!g->connection->connected()) return GQ_STREAM_STATE;
  QuicStream* s = g->session->Find(sid);
  if (s == nullptr) return GQ_STREAM_NOT_FOUND;
  if (s->type() == READ_UNIDIRECTIONAL) return GQ_STREAM_STATE;
  if (s->write_side_closed() || s->fin_buffered()) return GQ_STREAM_SHUT_WR;
  if (n == 0 && !fin) return GQ_OK;
  s->WriteOrBufferData(
      absl::string_view(reinterpret_cast<const char*>(data), n), fin != 0,
      nullptr);
  return GQ_OK;
}

int gq_shutdown_read(gq_conn* g, int64_t sid, uint64_t err) {
  if (!g->connection->connected()) return GQ_STREAM_STATE;
  QuicStream* s = g->session->Find(sid);
  if (s == nullptr) return GQ_STREAM_NOT_FOUND;
  if (s->type() == WRITE_UNIDIRECTIONAL) return GQ_STREAM_STATE;
  if (s->read_side_closed()) return GQ_OK;
  s->SendStopSending(QuicResetStreamError::FromIetf(err));
  s->StopReading();
  return GQ_OK;
}

int gq_shutdown_write(gq_conn* g, int64_t sid, uint64_t err) {
  if (!g->connection->connected()) return GQ_STREAM_STATE;
  QuicStream* s = g->session->Find(sid);
  if (s == nullptr) return GQ_STREAM_NOT_FOUND;
  if (s->type() == READ_UNIDIRECTIONAL) return GQ_STREAM_STATE;
  if (s->write_side_closed()) return GQ_OK;
  s->ResetWriteSide(QuicResetStreamError::FromIetf(err));
  return GQ_OK;
}

}  // extern "C"
