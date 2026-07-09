import DictatorshipTesting.Paper.Aux_Def_YoungDim
import DictatorshipTesting.Paper.Aux_Def_HOdd

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_10_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock`
-/

/-!
Paper statement: Definition 5.19 (`def:odd-matching-restriction-input`).
Title in paper: Odd matching-restriction scalar input.

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
