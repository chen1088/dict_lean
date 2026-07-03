import DictatorshipTesting.Paper.S05_Lem5_10_OneBoxCornerDecomposition_RowForm
import DictatorshipTesting.Paper.S05_Lem5_10_OneBoxCornerDecomposition_RemovableRow

/-!
Paper statement: Lemma 5.10 (`lem:one-box-corner-decomposition`)
Title in paper: One-box corner decomposition.

Status: main paper-facing file for the currently proved row-combinatorial
components of the one-box corner decomposition.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.10 row-form component. -/
theorem S05_Lem5_10_row_form
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_row_form h

/-- Lemma 5.10 unique-row component. -/
theorem S05_Lem5_10_row_form_unique
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    ∃! r : Nat,
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_row_form_unique h

/-- Lemma 5.10 removable-row component. -/
theorem S05_Lem5_10_removable_row
    {n k : Nat} {lam : YoungDiagram n} {mu : YoungDiagram k}
    (h : IsOneBoxChild lam mu) :
    exists r : Nat,
      IsRemovableRow lam r ∧
      youngRow lam r = youngRow mu r + 1 ∧
      forall s : Nat, s ≠ r -> youngRow lam s = youngRow mu s := by
  exact S05_oneBox_removable_row h

end DictatorshipTesting
