import DictatorshipTesting.Paper.S05_Def5_28_MatchingRestrictionOddInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_33_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Definition 5.32 (`def:odd-local-truncation-trace-input`).
Title in paper: Odd local-truncation trace input.

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
