import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDim
import DictatorshipTesting.Paper.Defs.S05_IntDef_HEven

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_TraceLocalTruncationEvenInput`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
-/

/-!

Status: definition/interface. This records the even scalar inequalities
extracted from the matching-restriction statement.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionEvenInput (m : Nat) : Prop :=
  forall lam : YoungDiagram (2 * m),
    0 <= hEven m lam /\ hEven m lam <= youngDim lam

end DictatorshipTesting
