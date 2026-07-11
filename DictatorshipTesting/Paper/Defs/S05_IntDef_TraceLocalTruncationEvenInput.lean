import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingRestrictionEvenInput

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!

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
