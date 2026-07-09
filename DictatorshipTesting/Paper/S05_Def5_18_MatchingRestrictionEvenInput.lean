import DictatorshipTesting.Paper.Aux_Def_YoungDim
import DictatorshipTesting.Paper.Aux_Def_HEven

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_10_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Definition 5.18 (`def:even-matching-restriction-input`).
Title in paper: Even matching-restriction scalar input.

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
