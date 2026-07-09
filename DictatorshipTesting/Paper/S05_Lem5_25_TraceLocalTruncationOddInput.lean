import DictatorshipTesting.Paper.S05_Lem5_23_MatchingRestrictionOddInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Lemma 5.25 (`lem:PM-trace-young-block`), odd trace-input
component.
Title in paper: Trace of one local truncation on one Young block.

Status: definition/interface. This records the scalar odd trace formula used by
the bridge layer.
-/

noncomputable section

namespace DictatorshipTesting

/-- Scalar trace formula for one odd Young block. -/
def TraceLocalTruncationOddInput (m : Nat) : Prop :=
  forall lam : YoungDiagram (2 * m + 1),
    exists traceLocalHigh : Real,
      traceLocalHigh = youngDim lam * hOdd m lam

end DictatorshipTesting
