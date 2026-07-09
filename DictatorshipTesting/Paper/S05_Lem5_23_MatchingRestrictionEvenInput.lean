import DictatorshipTesting.Paper.Aux_Def_YoungDim
import DictatorshipTesting.Paper.Aux_Def_HEven

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_23_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Lemma 5.23 (`lem:matching-restriction-X`), even scalar input
component.
Title in paper: Matching subgroup eigenbasis.

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
