/*
 * gquiche_shim.h -- a C face on Google QUICHE (Chrome's QUIC), for
 * harness/gquiche_driver.h.  Implemented by gquiche_shim.cc, which Bazel links
 * with QUICHE into libgquiche_shim.so (build_gquiche_harness.sh).
 *
 * All times are nanoseconds on the harness's clock (h->ts).
 */
#ifndef GQUICHE_SHIM_H
#define GQUICHE_SHIM_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct gq_conn gq_conn;

/* An endpoint at the end of its handshake: Handshake and 1-RTT keys of the stub
   cipher installed, the transport parameters of conn_driver.h's fill_params in
   both directions.  |local_cid| is ours, |remote_cid| the peer's.

   Between gq_new and gq_handshake_done a server must be given one Handshake
   packet (gq_recv): a QUICHE server validates its peer's address by decrypting
   one (RFC 9000 section 8.1), and until then the anti-amplification limit lets
   it send nothing at all.  gq_handshake_done completes the handshake and drops
   the Initial and Handshake keys, as QUICHE's TLS handshakers do; 0 on
   success. */
gq_conn *gq_new(int server, const uint8_t *local_cid, const uint8_t *remote_cid,
                size_t cidlen, uint64_t now);
int gq_handshake_done(gq_conn *g);
void gq_free(gq_conn *g);

void gq_set_clock(gq_conn *g, uint64_t now);

/* One UDP datagram from the peer. */
void gq_recv(gq_conn *g, const uint8_t *buf, size_t len);

/* As gq_recv. |ecn| is the model's numbering (0 not-ECT, 1 ECT(0), 2 ECT(1),
   3 CE). |alt| reads the datagram from the peer's second port. */
void gq_recv_meta(gq_conn *g, const uint8_t *buf, size_t len, int ecn, int alt);

/* Fires every alarm whose deadline is not after the clock, earliest first. */
void gq_fire_alarms(gq_conn *g);

/* Earliest alarm deadline, or UINT64_MAX. */
uint64_t gq_next_deadline(gq_conn *g);

/* Asks the connection to write whatever it has. */
void gq_can_write(gq_conn *g);

/* The next datagram QUICHE wrote, oldest first; 0 when there is none.
   |*dcidlen| is the length of the connection ID it was addressed to. */
size_t gq_pop_out(gq_conn *g, uint8_t *buf, size_t cap, size_t *dcidlen);

/* The next application-visible event as a trace line without the "CB  "
   prefix or newline, e.g. "recv_stream_data id=0 off=0 len=5 fin=0 early=0".
   Returns 0 when there is none. */
size_t gq_pop_event(gq_conn *g, char *buf, size_t cap);

/* 0 = open; -1 = closed without a QUIC transport error of ours (idle timeout,
   application close, closed by the peer); 1 + code = we closed with transport
   error |code|.  gq_close_detail is QUICHE's own reason, for the trace. */
int gq_status(gq_conn *g);
const char *gq_close_detail(gq_conn *g);

/* The new stream's ID, or -1 when the peer's stream limit forbids it. */
int64_t gq_open(gq_conn *g, int uni);

enum {
  GQ_OK = 0,
  GQ_STREAM_NOT_FOUND = -1,
  GQ_STREAM_SHUT_WR = -2,
  GQ_STREAM_STATE = -3
};

int gq_write(gq_conn *g, int64_t sid, const uint8_t *data, size_t n, int fin);
int gq_shutdown_read(gq_conn *g, int64_t sid, uint64_t err);
int gq_shutdown_write(gq_conn *g, int64_t sid, uint64_t err);

#ifdef __cplusplus
}
#endif

#endif /* GQUICHE_SHIM_H */
