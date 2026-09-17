/*
 * Differential harness: ngtcp2_frame_decoder_decode (C) vs Quic.decodeFrames
 * (Lean model).  Both sides render what they decoded into the same canonical
 * text; any difference aborts so libFuzzer records the input.
 *
 * Run on files:   ./frame_diff file...
 * Fuzz:           ./frame_diff corpus_dir
 * DIFF_SHOW=1 prints both renderings; DIFF_OUT=dir is where mismatching
 * inputs are saved.
 */
#include "diff_common.h"

extern lean_object *quic_model_dump_frames(lean_object *);
extern lean_object *quic_model_reencode(lean_object *);
extern uint8_t quic_model_roundtrip_ok(lean_object *);

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  (void)argc;
  (void)argv;
  model_init();
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  sbuf sb = {0};
  /* Exact-size heap copy so ASan sees any read past the payload. */
  uint8_t *copy = malloc(size ? size : 1);

  if (size) memcpy(copy, data, size);
  sb_reserve(&sb, 16);
  sb.p[0] = 0;
  int valid = c_dump_frames(&sb, copy, size) >= 0;
  sb_printf(&sb, valid ? "END\n" : "ERR\n");

  expect_same("frames", &sb, quic_model_dump_frames(model_bytes(data, size)),
              data, size);

  if (valid) {
    /* Encoder: the model re-encodes what it decoded.  (a) the model must get
       the same frames back from its own encoding; (b) ngtcp2 must read the
       model's encoding as the same frames it saw in the original. */
    sbuf orig = {0}, again = {0};
    lean_object *re;
    uint8_t *recopy;
    size_t relen;

    if (!quic_model_roundtrip_ok(model_bytes(data, size))) {
      fprintf(stderr, "MISMATCH (model decode . encode != id)\n");
      save_input("roundtrip", data, size);
      abort();
    }

    re = quic_model_reencode(model_bytes(data, size));
    relen = lean_sarray_size(re);
    recopy = malloc(relen ? relen : 1);
    if (relen) memcpy(recopy, lean_sarray_cptr(re), relen);
    lean_dec(re);

    g_show_n = 0;
    sb_reserve(&orig, 16);
    orig.p[0] = 0;
    sb_reserve(&again, 16);
    again.p[0] = 0;
    c_dump_frames(&orig, copy, size);
    if (c_dump_frames(&again, recopy, relen) < 0) sb_printf(&again, "ERR\n");
    g_show_n = 1;
    if (strcmp(orig.p, again.p) != 0) {
      fprintf(stderr, "MISMATCH (ngtcp2 on model-encoded frames)\n--- original\n%s--- re-encoded\n%s",
              orig.p, again.p);
      save_input("reencode", data, size);
      abort();
    }
    free(recopy);
    free(orig.p);
    free(again.p);
  }

  free(copy);
  free(sb.p);
  return 0;
}
