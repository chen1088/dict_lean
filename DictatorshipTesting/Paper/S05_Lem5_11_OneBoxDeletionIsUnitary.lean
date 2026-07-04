import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-!
Paper statement: Lemma 5.11 (`lem:one-box-deletion-unitary`)
Title in paper: One-box deletion is unitary.

Status: the Hilbert-space unitary statement is still future work.  This file
now proves the set-level bijection on the deleted tableau basis.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.11 set-level component: deleting the maximum-entry cell gives a
bijection from the remaining cells to `Fin n`. -/
theorem S05_Lem5_11_deleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) := by
  exact tableauDeleteMaxEntry_bijective T hu

/-- Compatibility short name for the set-level deletion bijection. -/
theorem S05_oneBox_deleteMaxEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    Function.Bijective (tableauDeleteMaxEntry T hu) := by
  exact S05_Lem5_11_deleteMaxEntry_bijective T hu

/-- Lemma 5.11 set-level component: deleted entries remain row-strict. -/
theorem S05_Lem5_11_deleteMaxEntry_row_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.row a.1 = YoungCell.row b.1 ->
      YoungCell.col a.1 < YoungCell.col b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  exact tableauDeleteMaxEntry_row_strict T hu

/-- Lemma 5.11 set-level component: deleted entries remain column-strict. -/
theorem S05_Lem5_11_deleteMaxEntry_col_strict {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    forall {a b : YoungCellExcept u},
      YoungCell.col a.1 = YoungCell.col b.1 ->
      YoungCell.row a.1 < YoungCell.row b.1 ->
      tableauDeleteMaxEntry T hu a < tableauDeleteMaxEntry T hu b := by
  exact tableauDeleteMaxEntry_col_strict T hu

/-- Lemma 5.11 set-level component: deleting the max cell gives a standard
tableau on the remaining cell set. -/
def S05_Lem5_11_deleteMaxAsStandardDeletedTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) {u : YoungCell lam}
    (hu : TableauMaxAt T u) :
    StandardDeletedTableau u :=
  deleteMaxAsStandardDeletedTableau T hu

end DictatorshipTesting
