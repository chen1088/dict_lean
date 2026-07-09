import DictatorshipTesting.Paper.S05_Lem5_23_MatchingRestrictionEvenInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Lemma 5.25 (`lem:PM-trace-young-block`), even trace-input
component.
Title in paper: Trace of one local truncation on one Young block.

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
