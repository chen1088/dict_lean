import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-!
Paper statement: Definition 5.7
Title in paper: One-box removals.

Status: re-exports the existing one-box child predicate and finite child sets.
-/

noncomputable section

namespace DictatorshipTesting

/-- One-box removals in the current finite Young-diagram model. -/
abbrev S05_IsOneBoxRemoval {n k : Nat}
    (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  IsOneBoxChild lam mu

/-- One-box children. -/
abbrev S05_oneBoxChildren {n : Nat} (lam : YoungDiagram n) :=
  oneBoxChildren lam

/-- Odd one-box children used by the Section 5 finite certificate. -/
abbrev S05_oneBoxChildrenOdd (m : Nat)
    (lam : YoungDiagram (2 * m + 1)) :=
  oneBoxChildrenOdd m lam

/-- Definition 5.7 row form: a one-box removal changes a unique row. -/
theorem S05_Def5_07_existsUnique_row_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact existsUnique_row_of_oneBoxChild h

/-- Definition 5.7 row form: a one-box removal deletes from a removable row. -/
theorem S05_Def5_07_exists_removableRow_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_removableRow_of_oneBoxChild h

end DictatorshipTesting
