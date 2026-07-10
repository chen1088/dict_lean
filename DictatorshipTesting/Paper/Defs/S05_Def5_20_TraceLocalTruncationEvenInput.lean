import DictatorshipTesting.Paper.Defs.S05_Def5_18_MatchingRestrictionEvenInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_13_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Definition 5.20 (`def:even-local-truncation-trace-input`).
Title in paper: Even local-truncation trace input.

Status: definition/interface. This records the scalar even trace formula used
by the bridge layer.
-/

noncomputable section

namespace DictatorshipTesting

/-- Scalar trace formula for one even Young block. -/
def TraceLocalTruncationEvenInput (m : Nat) : Prop :=
  forall lam : YoungDiagram (2 * m),
    exists traceLocalHigh : Real,
      traceLocalHigh = youngDim lam * hEven m lam

end DictatorshipTesting
