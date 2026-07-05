import DictatorshipTesting.Paper.S05_Lem5_10_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_02_DiagonalContentEigenspaces

/-!
Paper statement: Lemma 5.11 (`lem:one-box-deletion-intertwines`)
Title in paper: One-box deletion intertwines earlier swaps.

Status: the full Young-adjacent-operator intertwining statement is future
work.  This file proves the basis-level/content preservation and the
coordinate-level intertwining with the explicit diagonal content operators.
-/

noncomputable section

namespace DictatorshipTesting

theorem S05_Lem5_11_childCellToParent_cellOfEntry_deleteMax
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

theorem S05_Lem5_11_deleteMax_cellOfEntry_row
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

theorem S05_Lem5_11_deleteMax_cellOfEntry_col
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

theorem S05_Lem5_11_deleteMax_entryContent
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

/-- Lemma 5.11 basis-level component: deleting the maximum entry preserves the
content sequence on all remaining entries. -/
theorem S05_Lem5_11_deleteMax_tableauContentSequence
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

/-- Lemma 5.11 coordinate component: one-box deletion intertwines the diagonal
content operator for every entry that survives the deletion. -/
theorem S05_Lem5_11_deletionCoordinateMap_diagonalContent_intertwines
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (a : Fin n)
    (f : S05_Lem5_10_OneBoxDeletionCoordinateSpace h hr) :
    jucysMurphyDiagonalOperator a
        (S05_Lem5_10_deletionCoordinateMap h hr f)
      =
    S05_Lem5_10_deletionCoordinateMap h hr
      (fun T => (entryContent T.1 (Fin.castSucc a) : ℝ) * f T) := by
  funext S
  let e := S05_Lem5_10_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
    h hr
  change
    (entryContent S a : ℝ) * f (e.symm S) =
      (entryContent (e.symm S).1 (Fin.castSucc a) : ℝ) * f (e.symm S)
  have hdel :
      entryContent (e (e.symm S)) a =
        entryContent (e.symm S).1 (Fin.castSucc a) := by
    change
      entryContent
          (deleteMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr
            (deletedCornerCellOfOneBoxChildRow h hr)
            (deletedCornerCell_row h hr)
            (deletedCornerCell_col h hr)
            (e.symm S).1 (e.symm S).2) a =
        entryContent (e.symm S).1 (Fin.castSucc a)
    exact S05_Lem5_11_deleteMax_entryContent h hr
      (deletedCornerCellOfOneBoxChildRow h hr)
      (deletedCornerCell_row h hr)
      (deletedCornerCell_col h hr)
      (e.symm S).1 (e.symm S).2 a
  have hcontent :
      entryContent S a =
        entryContent (e.symm S).1 (Fin.castSucc a) := by
    simpa using hdel
  rw [hcontent]

end DictatorshipTesting
