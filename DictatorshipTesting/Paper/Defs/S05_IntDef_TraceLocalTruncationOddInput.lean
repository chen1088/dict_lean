import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionOddInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!

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
