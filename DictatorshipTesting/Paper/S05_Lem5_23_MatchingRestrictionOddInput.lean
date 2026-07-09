import DictatorshipTesting.Paper.S05_Def5_07_YoungDim
import DictatorshipTesting.Paper.S05_Def5_22_HOdd

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_23_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Lemma 5.23 (`lem:matching-restriction-X`), odd scalar input
component.
Title in paper: Matching subgroup eigenbasis.

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
