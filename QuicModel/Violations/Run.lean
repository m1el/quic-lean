import QuicModel.Violations.Trace
import QuicModel.Violations.Ack
import QuicModel.Violations.Stream
import QuicModel.Violations.Migration
import QuicModel.Violations.Termination
import QuicModel.Violations.Rest

/-!
  Feed every manufactured violation trace to the executable spec checker.
  A `Trace.required` row conforms only when the checker rejects it.
  A `Trace.recommended` row conforms only when ignoring the advice is still
  accepted. Those are different types, so one cannot be counted as the other.
-/
open Quic.Violations

def allChecks : List Trace :=
  Quic.Violations.Ack.checks ++
  Quic.Violations.Stream.checks ++
  Quic.Violations.Migration.checks ++
  Quic.Violations.Termination.checks ++
  Quic.Violations.Rest.checks

def main : IO UInt32 := do
  let mut requiredN := 0
  let mut requiredOk := 0
  let mut recommendedN := 0
  let mut recommendedOk := 0
  let mut uncheckedN := 0
  let mut failed : List String := []
  for t in allChecks do
    match t with
    | .required name .rejected =>
      requiredN := requiredN + 1
      requiredOk := requiredOk + 1
      IO.println s!"rejected         {name}"
    | .required name .accepted =>
      requiredN := requiredN + 1
      failed := name :: failed
      IO.println s!"ACCEPTED         {name}"
    | .recommended name .stillAccepted =>
      recommendedN := recommendedN + 1
      recommendedOk := recommendedOk + 1
      IO.println s!"advice allowed   {name}"
    | .recommended name .rejected =>
      recommendedN := recommendedN + 1
      failed := name :: failed
      IO.println s!"advice rejected  {name}"
    | .unchecked name =>
      uncheckedN := uncheckedN + 1
      IO.println s!"no checker       {name}"
  IO.println ""
  IO.println s!"required rejected {requiredOk}/{requiredN}"
  IO.println s!"recommended still accepted {recommendedOk}/{recommendedN}"
  IO.println s!"unchecked {uncheckedN}"
  IO.println s!"total traces {allChecks.length}"
  if failed.isEmpty && allChecks.all Trace.conforms then
    return 0
  else
    IO.println s!"FAILED {failed.length}"
    return 1
