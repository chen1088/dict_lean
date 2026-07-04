import DictatorshipTesting.Paper.S05_Lem5_11_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_02_JucysMurphyEigenbasis

/-!
Paper statement: Lemma 5.12 (`lem:one-box-deletion-intertwines`)
Title in paper: One-box deletion intertwines earlier swaps.

Status: the full Young-operator intertwining statement is future work.  This
file proves the basis-level/content preservation needed for that statement.
-/

noncomputable section

namespace DictatorshipTesting

theorem S05_Lem5_12_childCellToParent_cellOfEntry_deleteMax
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u)
    (a : Fin n) :
    childCellToParentCellOfOneBoxChildRow h hr
      (cellOfEntry
        (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr u hu_row hu_col T hu) a)
      =
    cellOfEntry T (Fin.castSucc a) := by
  exact childCellToParent_cellOfEntry_deleteMax h hr u hu_row hu_col T hu a

theorem S05_Lem5_12_deleteMax_cellOfEntry_row
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u)
    (a : Fin n) :
    YoungCell.row
      (cellOfEntry
        (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr u hu_row hu_col T hu) a)
      =
    YoungCell.row (cellOfEntry T (Fin.castSucc a)) := by
  exact deleteMax_cellOfEntry_row h hr u hu_row hu_col T hu a

theorem S05_Lem5_12_deleteMax_cellOfEntry_col
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u)
    (a : Fin n) :
    YoungCell.col
      (cellOfEntry
        (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr u hu_row hu_col T hu) a)
      =
    YoungCell.col (cellOfEntry T (Fin.castSucc a)) := by
  exact deleteMax_cellOfEntry_col h hr u hu_row hu_col T hu a

theorem S05_Lem5_12_deleteMax_entryContent
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u)
    (a : Fin n) :
    entryContent
      (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
        h hr u hu_row hu_col T hu) a
      =
    entryContent T (Fin.castSucc a) := by
  exact deleteMax_entryContent h hr u hu_row hu_col T hu a

/-- Lemma 5.12 basis-level component: deleting the maximum entry preserves the
content sequence on all remaining entries. -/
theorem S05_Lem5_12_deleteMax_tableauContentSequence
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (u : YoungCell lam)
    (hu_row : YoungCell.row u = r)
    (hu_col : YoungCell.col u = youngRow mu r)
    (T : StandardYoungTableau lam)
    (hu : TableauMaxAt T u)
    (a : Fin n) :
    tableauContentSequence
        (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr u hu_row hu_col T hu) a
      =
    tableauContentSequence T (Fin.castSucc a) := by
  exact deleteMax_entryContent h hr u hu_row hu_col T hu a

end DictatorshipTesting
