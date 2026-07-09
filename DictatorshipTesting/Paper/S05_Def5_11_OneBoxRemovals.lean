import DictatorshipTesting.Paper.Aux_YoungDiagramCorners

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Definition 5.11 (`def:one-box-removals`)
Title in paper: One-box removals.

Status: definition/interface. Re-exports the existing one-box child predicate and finite child sets.
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

/-- Definition 5.9 row form: a one-box removal changes a unique row. -/
theorem S05_Def5_11_existsUnique_row_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact existsUnique_row_of_oneBoxChild h

/-- Definition 5.9 row form: a one-box removal deletes from a removable row. -/
theorem S05_Def5_11_exists_removableRow_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact exists_removableRow_of_oneBoxChild h

/-- Definition 5.9 row fact: a one-box removal has total row difference `1`. -/
theorem S05_Def5_11_sum_row_diff_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    (Finset.range n).sum (fun i => youngRow lam i - youngRow mu i) = 1 := by
  exact sum_row_diff_of_oneBoxChild h

/-- Definition 5.9 corner form: a one-box removal deletes a removable corner. -/
theorem S05_Def5_11_exists_removableCornerBox_of_oneBoxRemoval
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : S05_IsOneBoxRemoval lam mu) :
    exists u : Nat × Nat,
      IsRemovableCornerBox lam u ∧
      u.2 = youngRow mu u.1 ∧
      youngRow lam u.1 = youngRow mu u.1 + 1 ∧
      forall s : Nat, s ≠ u.1 -> youngRow lam s = youngRow mu s := by
  exact exists_removableCornerBox_of_oneBoxChild h

end DictatorshipTesting
