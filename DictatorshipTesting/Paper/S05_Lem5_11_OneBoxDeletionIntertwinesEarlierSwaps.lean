import DictatorshipTesting.Paper.S05_Lem5_10_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_02_DiagonalContentEigenspaces

/-!
Paper statement: Lemma 5.11 (`lem:one-box-deletion-intertwines`)
Title in paper: One-box deletion intertwines earlier swaps.

Status: the full coordinate-level Young-adjacent-operator intertwining
statement is future work.  This file proves basis-level content preservation,
the row/column and coefficient preservation for earlier adjacent pairs under
one-box insertion, and the coordinate-level intertwining with the explicit
diagonal content operators.
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

/-- Reindexing helper for the lower entry of an earlier adjacent pair after
one-box insertion. -/
theorem S05_Lem5_11_castSucc_adjacentEntryLo
    {n : Nat} (a : Fin n) :
    Fin.castSucc (adjacentEntryLo a) =
      adjacentEntryLo (Fin.castSucc a) := by
  rfl

/-- Reindexing helper for the upper entry of an earlier adjacent pair after
one-box insertion. -/
theorem S05_Lem5_11_castSucc_adjacentEntryHi
    {n : Nat} (a : Fin n) :
    Fin.castSucc (adjacentEntryHi a) =
      adjacentEntryHi (Fin.castSucc a) := by
  apply Fin.ext
  simp [adjacentEntryHi]

/-- Lemma 5.11 row component: inserting the maximum box preserves the row of
the lower entry in every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_adjacentLoCell_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    YoungCell.row (adjacentLoCell S a) =
      YoungCell.row
        (adjacentLoCell
          (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hrow := S05_Lem5_11_deleteMax_cellOfEntry_row h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryLo a)
  have hdel := S05_Lem5_10_delete_insert h hr S
  simp [S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hrow
  rw [S05_Lem5_11_castSucc_adjacentEntryLo a] at hrow
  simpa [adjacentLoCell,
    S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hrow

/-- Lemma 5.11 column component: inserting the maximum box preserves the
column of the lower entry in every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_adjacentLoCell_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    YoungCell.col (adjacentLoCell S a) =
      YoungCell.col
        (adjacentLoCell
          (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hcol := S05_Lem5_11_deleteMax_cellOfEntry_col h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryLo a)
  have hdel := S05_Lem5_10_delete_insert h hr S
  simp [S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcol
  rw [S05_Lem5_11_castSucc_adjacentEntryLo a] at hcol
  simpa [adjacentLoCell,
    S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hcol

/-- Lemma 5.11 row component: inserting the maximum box preserves the row of
the upper entry in every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_adjacentHiCell_row
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    YoungCell.row (adjacentHiCell S a) =
      YoungCell.row
        (adjacentHiCell
          (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hrow := S05_Lem5_11_deleteMax_cellOfEntry_row h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryHi a)
  have hdel := S05_Lem5_10_delete_insert h hr S
  simp [S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hrow
  rw [S05_Lem5_11_castSucc_adjacentEntryHi a] at hrow
  simpa [adjacentHiCell,
    S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hrow

/-- Lemma 5.11 column component: inserting the maximum box preserves the
column of the upper entry in every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_adjacentHiCell_col
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    YoungCell.col (adjacentHiCell S a) =
      YoungCell.col
        (adjacentHiCell
          (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hcol := S05_Lem5_11_deleteMax_cellOfEntry_col h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryHi a)
  have hdel := S05_Lem5_10_delete_insert h hr S
  simp [S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcol
  rw [S05_Lem5_11_castSucc_adjacentEntryHi a] at hcol
  simpa [adjacentHiCell,
    S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hcol

/-- Lemma 5.11 geometric component: one-box insertion preserves whether an
earlier adjacent pair lies in a common row. -/
theorem S05_Lem5_11_insertMax_adjacentSameRow_iff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentSameRow
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) ↔
      adjacentSameRow S a := by
  constructor
  · intro hrow
    have hlo := S05_Lem5_11_insertMax_adjacentLoCell_row h hr S a
    have hhi := S05_Lem5_11_insertMax_adjacentHiCell_row h hr S a
    unfold adjacentSameRow at *
    rw [hlo, hhi]
    exact hrow
  · intro hrow
    have hlo := S05_Lem5_11_insertMax_adjacentLoCell_row h hr S a
    have hhi := S05_Lem5_11_insertMax_adjacentHiCell_row h hr S a
    unfold adjacentSameRow at *
    rw [← hlo, ← hhi]
    exact hrow

/-- Lemma 5.11 geometric component: one-box insertion preserves whether an
earlier adjacent pair lies in a common column. -/
theorem S05_Lem5_11_insertMax_adjacentSameCol_iff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentSameCol
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) ↔
      adjacentSameCol S a := by
  constructor
  · intro hcol
    have hlo := S05_Lem5_11_insertMax_adjacentLoCell_col h hr S a
    have hhi := S05_Lem5_11_insertMax_adjacentHiCell_col h hr S a
    unfold adjacentSameCol at *
    rw [hlo, hhi]
    exact hcol
  · intro hcol
    have hlo := S05_Lem5_11_insertMax_adjacentLoCell_col h hr S a
    have hhi := S05_Lem5_11_insertMax_adjacentHiCell_col h hr S a
    unfold adjacentSameCol at *
    rw [← hlo, ← hhi]
    exact hcol

/-- Lemma 5.11 content component: inserting the maximum box preserves the
content of every surviving entry. -/
theorem S05_Lem5_11_insertMax_entryContent_castSucc
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    entryContent S a =
      entryContent
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  have hcontent := S05_Lem5_11_deleteMax_entryContent h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    a
  have hdel := S05_Lem5_10_delete_insert h hr S
  simp [S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcontent
  exact hcontent

/-- Lemma 5.11 coefficient component: one-box insertion preserves the axial
distance of every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_adjacentAxialDistance
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentAxialDistance S a =
      adjacentAxialDistance
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  unfold adjacentAxialDistance
  rw [S05_Lem5_11_insertMax_entryContent_castSucc h hr S (adjacentEntryHi a)]
  rw [S05_Lem5_11_insertMax_entryContent_castSucc h hr S (adjacentEntryLo a)]
  rw [S05_Lem5_11_castSucc_adjacentEntryHi a]
  rw [S05_Lem5_11_castSucc_adjacentEntryLo a]

/-- Lemma 5.11 coefficient component: one-box insertion preserves the diagonal
Young-adjacent coefficient for every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_youngAdjacentDiagCoeff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    youngAdjacentDiagCoeff S a =
      youngAdjacentDiagCoeff
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  rw [youngAdjacentDiagCoeff, youngAdjacentDiagCoeff,
    S05_Lem5_11_insertMax_adjacentAxialDistance h hr S a]

/-- Lemma 5.11 coefficient component: one-box insertion preserves the
off-diagonal Young-adjacent coefficient for every earlier adjacent pair. -/
theorem S05_Lem5_11_insertMax_youngAdjacentOffCoeff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    youngAdjacentOffCoeff S a =
      youngAdjacentOffCoeff
        (S05_Lem5_10_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    S05_Lem5_11_insertMax_youngAdjacentDiagCoeff h hr S a]

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
