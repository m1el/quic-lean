import QuicModel.Spec.Endpoint.Exports

/-!
The composed endpoint (WP12): `QuicModel/Spec/Endpoint/*`.

  Lemmas → Basic → Merge → Dispatch → Pipeline → Events → Send → Component →
  Obligations → Theorems → Exports

`Endpoint.component prot` is a `Component` whose `Step` is, by definition,
membership in `outcomes` (the composition layer is glue; the specification
content lives in the components it composes, and `Theorems.lean` projects every
reachable endpoint state to a reachable state of each of them).  The examples
layer (replaying `harness/scripts/*` through `Endpoint.step`) is not yet written.
-/
