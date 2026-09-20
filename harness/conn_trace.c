/*
 * conn_trace -- drive a real ngtcp2_conn with stubbed crypto and record an
 * observable trace (WP8).  No Lean is called; the model side (WP13) consumes
 * the text trace this produces.
 *
 * ===========================================================================
 * 1. Fixed setup
 * ===========================================================================
 *
 * Crypto is the same stub as harness/pkt_diff.c and Quic.Protection.stub:
 *   encrypt  : payload stays in the clear, tag = 16 bytes of 0xA5
 *   decrypt  : verifies nothing, strips the last 16 bytes
 *   hp_mask  : mask = the first 5 bytes of the 16-byte sample
 * The same three keys (Initial, Handshake, 1-RTT) are installed directly, as
 * ngtcp2's own fuzz/read_write_pkt.cc does, and the connection is forced into
 * the post-handshake state.  No TLS is involved anywhere.
 *
 * Transport parameters, identical for the local and the remote side, chosen
 * small so that every limit is reachable from a short script:
 *
 *   | parameter                          | value     | why                   |
 *   |------------------------------------|-----------|-----------------------|
 *   | initial_max_data                   | 4096      | conn flow control     |
 *   | initial_max_stream_data_bidi_local | 1024      | stream flow control   |
 *   | initial_max_stream_data_bidi_remote| 1024      | stream flow control   |
 *   | initial_max_stream_data_uni        | 1024      | stream flow control   |
 *   | initial_max_streams_bidi           | 4         | stream limit          |
 *   | initial_max_streams_uni            | 2         | stream limit          |
 *   | max_idle_timeout                   | 30 s      | idle close reachable  |
 *   | max_udp_payload_size               | 1200      | minimum ngtcp2 accepts|
 *   | active_connection_id_limit         | 4         | CID limit reachable   |
 *   | ack_delay_exponent                 | 3         | RFC 9000 default      |
 *   | max_ack_delay                      | 25 ms     | RFC 9000 default      |
 *   | max_datagram_frame_size            | 1200      | DATAGRAM enabled      |
 *   | disable_active_migration           | 0         |                       |
 *   | grease_quic_bit                    | 0         | fixed bit always set  |
 *   | stateless_reset_token              | absent    |                       |
 *
 *   settings: initial_ts 0, initial_rtt 100 ms, handshake_timeout infinite,
 *   no_pmtud 1, initial_pkt_num 0, cc_algo RENO, no qlog, no logging.
 *
 * Connection IDs are fixed 8-byte values:
 *   local  SCID = a0 a1 a2 a3 a4 a5 a6 a7   (the peer addresses us with this)
 *   remote SCID = b0 b1 b2 b3 b4 b5 b6 b7   (= our DCID, = remote initial_scid,
 *                                            = original_dcid when we are client)
 * The path is fixed: 127.0.0.1:4433 (local) <-> 127.0.0.1:12345 (remote).
 * The `rand` callback is a fixed LCG reset at the start of every run.
 * The clock never advances by itself: `ts` only moves when a step says so.
 *
 * ===========================================================================
 * 2. Script grammar (./out/conn_trace --script FILE)
 * ===========================================================================
 *
 * One step per line.  `#` starts a comment, blank lines are ignored.
 * Numbers are decimal unless prefixed with 0x.  <sid> is either a decimal
 * stream id or the word `last` (the stream most recently opened locally).
 *
 *   role server|client        role of the connection under test.  Must come
 *                             before any other step; default is `server`.
 *   recv <space> <pn> <hex>   the PEER sends a packet: a well-formed protected
 *                             packet is built with ngtcp2_ppe in <space>
 *                             (initial|handshake|app) with packet number <pn>,
 *                             carrying the frames that ngtcp2's frame decoder
 *                             makes of <hex> (re-encoded by ngtcp2's encoder,
 *                             exactly as pkt_diff.c's roundtrip mode does).
 *                             An empty payload becomes a single PING.
 *                             Packet numbers inside an ACK frame are ordinals:
 *                             k is the k-th packet the endpoint has sent in
 *                             <space>, from 0 (conn_driver.h, "engine-neutral
 *                             references"); under ngtcp2, which numbers from 0
 *                             without gaps, that is the number itself.
 *                             The packet is fed to ngtcp2_conn_read_pkt.
 *                             An Initial is padded to 1200 bytes.
 *   time <us>                 advance the clock by <us> microseconds and call
 *                             ngtcp2_conn_handle_expiry.
 *   open bidi|uni             ngtcp2_conn_open_{bidi,uni}_stream.
 *   write <sid> <n> <fin>     write <n> bytes of filler ('a'+i%26) on <sid>,
 *                             with FIN if <fin> is 1; each resulting packet is
 *                             traced.
 *   shutdown_read  <sid> <e>  ngtcp2_conn_shutdown_stream_read (STOP_SENDING).
 *   shutdown_write <sid> <e>  ngtcp2_conn_shutdown_stream_write (RESET_STREAM).
 *   shutdown       <sid> <e>  ngtcp2_conn_shutdown_stream (both).
 *   extend_stream <sid> <n>   ngtcp2_conn_extend_max_stream_offset.
 *   extend_conn <n>           ngtcp2_conn_extend_max_offset.
 *   extend_streams bidi|uni <n>  ngtcp2_conn_extend_max_streams_{bidi,uni}.
 *   drain                     call ngtcp2_conn_write_pkt until it returns 0,
 *                             tracing every packet written.
 *
 * ===========================================================================
 * 3. Trace grammar (one record per line, in the order things happened)
 * ===========================================================================
 *
 *   CONN role=<server|client> scid=<hex> dcid=<hex>
 *       once, first line.
 *   IN  space=<initial|handshake|app> pn=<n> len=<bytes> frames=[<f>;<f>;...]
 *       a packet handed to ngtcp2_conn_read_pkt; <f> is the canonical frame
 *       rendering of diff_common.h's dump_frame (= QuicModel/Dump.lean).
 *       The frames shown are the packet's actual plaintext, so PADDING that
 *       the writer added is visible.
 *   CB  <name> <k=v>...
 *       an application-visible callback fired.  These are the model's Effects.
 *       Names and arguments:
 *         recv_stream_data id= off= len= fin= early=
 *         acked_stream_data_offset id= off= len=
 *         stream_open id=
 *         stream_close id= app_error_code= set=      (set=0: no code given)
 *         stream_close2 id= rx_app_error_code= tx_app_error_code= set=
 *         stream_reset id= final_size= app_error_code=
 *         stream_stop_sending id= app_error_code=
 *         recv_stop_sending id= app_error_code=
 *         extend_max_local_streams_bidi|uni max_streams=
 *         extend_max_remote_streams_bidi|uni max_streams=
 *         extend_max_stream_data id= max_data=
 *         extend_max_data max_data=
 *         recv_datagram len= early=
 *         ack_datagram dgram_id=      lost_datagram dgram_id=
 *         handshake_completed         handshake_confirmed
 *         recv_crypto_data level= off= len=
 *         recv_new_token token=<hex>
 *         recv_retry / recv_version_negotiation / recv_stateless_reset[2]
 *         path_validation flags= res=<success|failure|aborted>
 *         begin_path_validation flags=
 *         dcid_status type=<activate|deactivate> seq= cid=<hex>
 *         dcid_status2 type= seq= cid=<hex>
 *         get_new_connection_id cidlen= -> cid=<hex>
 *         get_new_connection_id2 cidlen= -> cid=<hex>
 *         remove_connection_id cid=<hex>
 *         get_path_challenge_data[2] -> data=<hex>
 *         select_preferred_addr / update_key / version_negotiation version=
 *         recv_rx_key level= / recv_tx_key level= / tls_early_data_rejected
 *         client_initial / recv_client_initial dcid=<hex>
 *   RET <call>=<NGTCP2_ERR_... | OK>
 *       the library return code of the call the step made.
 *   ERR type=<transport|application|version_negotiation|idle_close|drop_conn|
 *             retry> code=<n> frame_type=<n> reason=<hex>
 *       what ngtcp2_ccerr_set_liberr makes of a failing return code: the QUIC
 *       error code ngtcp2 would actually close with.  Followed by the
 *       CONNECTION_CLOSE packet from ngtcp2_conn_write_connection_close (as an
 *       ordinary OUT record; nothing is written for an idle close).  After
 *       this the script stops.
 *   OUT space=<initial|handshake|app> pn=<n> len=<bytes> frames=[<f>;<f>;...]
 *       a packet the connection wrote.  The harness unprotects it with the
 *       stub crypto (mask = first 5 bytes of the sample, tag = last 16 bytes)
 *       and dumps its frames with the same canonical rendering.  `len` is the
 *       protected packet length, so the datagram-size rules of Sec. 14 are
 *       visible.  A coalesced datagram produces one OUT record per packet.
 *   TIME now=<us> expiry=<us|none>
 *       after every step.
 *   SUM <16 hex digits>
 *       FNV-1a over everything above; the last line.
 *
 * Determinism: no pointers, no wall clock, no addresses are printed; the only
 * randomness is the fixed LCG.  The same input always yields the same bytes.
 *
 * ===========================================================================
 * 4. Fuzzer entry
 * ===========================================================================
 *
 * LLVMFuzzerTestOneInput reads the input as the same script in binary:
 *   byte 0        bit 0: 0 = server, 1 = client
 *   then, until the input runs out or 64 steps have run, one step each:
 *     op byte, op % 11 selects: 0,1 recv | 2 time | 3 open | 4 write
 *     | 5 shutdown | 6 extend | 7,8 drain | 9 write on a fresh stream | 10 recv
 *   operand bytes follow as the decoder below says; a truncated input reads 0.
 */
#include "conn_driver.h"

/* ----------------------------------------------------------------- entry */

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  int i;
  for (i = 1; i < *argc; ++i) {
    if (strcmp((*argv)[i], "--script") == 0) {
      if (i + 1 >= *argc) {
        fprintf(stderr, "conn_trace: --script needs a file\n");
        exit(2);
      }
      exit(run_script((*argv)[i + 1]));
    }
  }
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  harness h;
  int server;

  if (size < 2) return 0;
  server = !(data[0] & 1);
  harness_start(&h, server);
  if (setup_conn(&h, server) != 0) {
    free(h.tr.p);
    return 0;
  }
  tr_time(&h);
  run_binary(&h, data + 1, size - 1);
  harness_finish(&h, getenv("TRACE_SHOW") != NULL);
  return 0;
}
