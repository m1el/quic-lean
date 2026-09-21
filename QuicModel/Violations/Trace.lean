/-!
  Accepted behavior and recommended behavior are different claims.

  `Component.accepts` and `maySend` answer only the first: is this outcome
  among the ones `Step` permits? That answer is a `Bool`, and it has to be,
  because permission is yes or no. A SHOULD lives in a separate `Recommended`
  predicate precisely so that ignoring it stays inside `Step`. Folding both
  answers into one `Bool` (or into a name prefix) erases which claim was tested.

  A trace therefore carries its force as a constructor. A required trace holds
  a `Requirement` and cannot record "advice ignored". A recommended trace holds
  a `Recommendation` and cannot record "this was a MUST".
-/
namespace Quic.Violations

/-- What a MUST / MUST NOT violation did under `accepts` / `maySend`. -/
inductive Requirement where
  /-- The checker refused the behavior. A conforming endpoint cannot do it. -/
  | rejected
  /-- The checker permitted the behavior. The MUST is not being enforced. -/
  | accepted
  deriving DecidableEq, Repr

/-- What ignoring a SHOULD / MAY did. Both constructors are still conforming
    or not for a different reason than `Requirement`: rejection here means the
    checker is stricter than the text. -/
inductive Recommendation where
  /-- Ignoring the advice is still in `Step`. -/
  | stillAccepted
  /-- The checker refused a behavior the text only recommends against. -/
  | rejected
  deriving DecidableEq, Repr

inductive Trace where
  | required (name : String) (ruling : Requirement)
  | recommended (name : String) (ruling : Recommendation)
  | unchecked (name : String)
  deriving Repr

/-- `rejected = true` means the executable checker refused the behavior. -/
def must (name : String) (rejected : Bool) : Trace :=
  .required name (if rejected then .rejected else .accepted)

/-- `rejected = true` means the checker refused a behavior that is only advice. -/
def advice (name : String) (rejected : Bool) : Trace :=
  .recommended name (if rejected then .rejected else .stillAccepted)

def unchecked (name : String) : Trace :=
  .unchecked name

def Trace.name : Trace → String
  | .required name _ => name
  | .recommended name _ => name
  | .unchecked name => name

/-- A required violation must be refused. Ignoring a recommendation must not be. -/
def Trace.conforms : Trace → Bool
  | .required _ .rejected => true
  | .required _ .accepted => false
  | .recommended _ .stillAccepted => true
  | .recommended _ .rejected => false
  | .unchecked _ => true

end Quic.Violations
