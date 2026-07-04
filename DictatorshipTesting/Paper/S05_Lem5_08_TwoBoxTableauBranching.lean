import DictatorshipTesting.Paper.S05_Def5_06_SignedTwoBoxRemovals
import DictatorshipTesting.Paper.S05_Lem5_11_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_12_OneBoxDeletionIntertwinesEarlierSwaps

/-!
Paper statement: Lemma 5.8 (`lem:two-box-tableau-branching`)
Title in paper: Two-box tableau branching.

Status: paper-facing owner file for the rewritten Section 5 statement.  The
current Lean development contains the scalar dimension shadow later in Lemma
5.15, but not the full tableau/Specht branching theorem.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.8 set-level component: perform the first one-box deletion in an
iterated two-box tableau deletion. -/
def S05_Lem5_08_deleteFirstMaxAsTableau
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    StandardYoungTableau mu :=
  deleteMaxAsStandardYoungTableauOfOneBoxChildRow
    h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    T hu

/-- Lemma 5.8 set-level component: the first deleted cell is a removable corner
of the parent tableau shape. -/
theorem S05_Lem5_08_first_deleted_cell_removable_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    IsRemovableCornerBox lam
      (YoungCell.toNatPair (deletedCornerCellOfOneBoxChildRow h hr)) := by
  exact removableCornerBox_of_tableauMaxAt T hu

/-- Lemma 5.8 set-level component: after deleting the largest entry, the new
largest entry lies in a unique removable corner of the child shape. -/
theorem S05_Lem5_08_after_first_deletion_unique_second_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)) :
    ∃! v : YoungCell mu,
      TableauMaxAt (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) v ∧
        IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact existsUnique_removableCornerBox_tableauMaxAt
    (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu)

/-- Lemma 5.8 set-level component: any second maximum-entry cell after the first
deletion is a removable corner of the child shape. -/
theorem S05_Lem5_08_second_deleted_cell_removable_corner
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    {v : YoungCell mu}
    (hv : TableauMaxAt (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) v) :
    IsRemovableCornerBox mu (YoungCell.toNatPair v) := by
  exact removableCornerBox_of_tableauMaxAt
    (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) hv

/-- Lemma 5.8 basis-level component: the first deletion in the two-box
branching step preserves the content sequence on the remaining entries. -/
theorem S05_Lem5_08_first_deletion_tableauContentSequence
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    tableauContentSequence (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) a =
      tableauContentSequence T (Fin.castSucc a) := by
  exact S05_Lem5_12_deleteMax_tableauContentSequence
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.8 basis-level component: after the first deletion, the child cell
containing a remaining entry maps back to the original parent cell. -/
theorem S05_Lem5_08_first_deletion_childCellToParent_cellOfEntry
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    childCellToParentCellOfOneBoxChildRow h hr
      (cellOfEntry (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) a)
      =
    cellOfEntry T (Fin.castSucc a) := by
  exact S05_Lem5_12_childCellToParent_cellOfEntry_deleteMax
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.8 basis-level component: the first deletion preserves the row of
each remaining entry. -/
theorem S05_Lem5_08_first_deletion_cellOfEntry_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    YoungCell.row
      (cellOfEntry (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_Lem5_12_deleteMax_cellOfEntry_row
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

/-- Lemma 5.8 basis-level component: the first deletion preserves the column of
each remaining entry. -/
theorem S05_Lem5_08_first_deletion_cellOfEntry_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr))
    (a : Fin (n + 1)) :
    YoungCell.col
      (cellOfEntry (S05_Lem5_08_deleteFirstMaxAsTableau h hr T hu) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc a)) := by
  exact S05_Lem5_12_deleteMax_cellOfEntry_col
    h hr (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr) (deletedCornerCell_col h hr) T hu a

end DictatorshipTesting
