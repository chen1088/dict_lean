import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDim
import DictatorshipTesting.Paper.Defs.S05_IntDef_HOdd

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_IntDef_TraceLocalTruncationOddInput`
- `DictatorshipTesting.Paper.S05_Lem5_20_MatchingSubgroupEigenbasis`
-/

/-!

Status: definition/interface. This records the odd scalar inequalities
extracted from the matching-restriction statement.
-/

noncomputable section

namespace DictatorshipTesting

/-- Odd matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionOddInput (m : Nat) : Prop :=
  forall lam : YoungDiagram (2 * m + 1),
    0 <= hOdd m lam /\ hOdd m lam <= youngDim lam

end DictatorshipTesting
