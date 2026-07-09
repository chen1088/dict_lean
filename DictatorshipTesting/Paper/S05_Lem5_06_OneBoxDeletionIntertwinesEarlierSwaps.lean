import DictatorshipTesting.Paper.S05_Lem5_05_OneBoxDeletionIsUnitary
import DictatorshipTesting.Paper.S05_Lem5_02_DiagonalContentEigenspaces

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_03_TwoBoxTableauBranching`
-/


/-!
Paper statement: Lemma 5.6 (`lem:one-box-deletion-intertwines`)
Title in paper: One-box deletion intertwines earlier swaps.

Status: proven. Proved for the concrete deletion-fiber coordinate model.  This file
proves basis-level content preservation, row/column and matrix-coefficient
preservation for earlier adjacent pairs under one-box insertion, and the
coordinate-level intertwining with both the explicit Young-adjacent operators
on the deletion fiber and the diagonal content operators.
-/

noncomputable section

namespace DictatorshipTesting

theorem S05_Lem5_06_childCellToParent_cellOfEntry_deleteMax
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

theorem S05_Lem5_06_deleteMax_cellOfEntry_row
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

theorem S05_Lem5_06_deleteMax_cellOfEntry_col
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

theorem S05_Lem5_06_deleteMax_entryContent
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

/-- Lemma 5.4 basis-level component: deleting the maximum entry preserves the
content sequence on all remaining entries. -/
theorem S05_Lem5_06_deleteMax_tableauContentSequence
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
theorem S05_Lem5_06_castSucc_adjacentEntryLo
    {n : Nat} (a : Fin n) :
    Fin.castSucc (adjacentEntryLo a) =
      adjacentEntryLo (Fin.castSucc a) := by
  rfl

/-- Reindexing helper for the upper entry of an earlier adjacent pair after
one-box insertion. -/
theorem S05_Lem5_06_castSucc_adjacentEntryHi
    {n : Nat} (a : Fin n) :
    Fin.castSucc (adjacentEntryHi a) =
      adjacentEntryHi (Fin.castSucc a) := by
  apply Fin.ext
  simp [adjacentEntryHi]

/-- Lemma 5.4 row component: inserting the maximum box preserves the row of
the lower entry in every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_adjacentLoCell_row
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
          (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hrow := S05_Lem5_06_deleteMax_cellOfEntry_row h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryLo a)
  have hdel := S05_Lem5_05_delete_insert h hr S
  simp [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hrow
  rw [S05_Lem5_06_castSucc_adjacentEntryLo a] at hrow
  simpa [adjacentLoCell,
    S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hrow

/-- Lemma 5.4 column component: inserting the maximum box preserves the
column of the lower entry in every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_adjacentLoCell_col
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
          (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hcol := S05_Lem5_06_deleteMax_cellOfEntry_col h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryLo a)
  have hdel := S05_Lem5_05_delete_insert h hr S
  simp [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcol
  rw [S05_Lem5_06_castSucc_adjacentEntryLo a] at hcol
  simpa [adjacentLoCell,
    S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hcol

/-- Lemma 5.4 row component: inserting the maximum box preserves the row of
the upper entry in every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_adjacentHiCell_row
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
          (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hrow := S05_Lem5_06_deleteMax_cellOfEntry_row h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryHi a)
  have hdel := S05_Lem5_05_delete_insert h hr S
  simp [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hrow
  rw [S05_Lem5_06_castSucc_adjacentEntryHi a] at hrow
  simpa [adjacentHiCell,
    S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hrow

/-- Lemma 5.4 column component: inserting the maximum box preserves the
column of the upper entry in every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_adjacentHiCell_col
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
          (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr S) (Fin.castSucc a)) := by
  have hcol := S05_Lem5_06_deleteMax_cellOfEntry_col h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    (adjacentEntryHi a)
  have hdel := S05_Lem5_05_delete_insert h hr S
  simp [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcol
  rw [S05_Lem5_06_castSucc_adjacentEntryHi a] at hcol
  simpa [adjacentHiCell,
    S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using hcol

/-- Lemma 5.4 geometric component: one-box insertion preserves whether an
earlier adjacent pair lies in a common row. -/
theorem S05_Lem5_06_insertMax_adjacentSameRow_iff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentSameRow
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) ↔
      adjacentSameRow S a := by
  constructor
  · intro hrow
    have hlo := S05_Lem5_06_insertMax_adjacentLoCell_row h hr S a
    have hhi := S05_Lem5_06_insertMax_adjacentHiCell_row h hr S a
    unfold adjacentSameRow at *
    rw [hlo, hhi]
    exact hrow
  · intro hrow
    have hlo := S05_Lem5_06_insertMax_adjacentLoCell_row h hr S a
    have hhi := S05_Lem5_06_insertMax_adjacentHiCell_row h hr S a
    unfold adjacentSameRow at *
    rw [← hlo, ← hhi]
    exact hrow

/-- Lemma 5.4 geometric component: one-box insertion preserves whether an
earlier adjacent pair lies in a common column. -/
theorem S05_Lem5_06_insertMax_adjacentSameCol_iff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentSameCol
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) ↔
      adjacentSameCol S a := by
  constructor
  · intro hcol
    have hlo := S05_Lem5_06_insertMax_adjacentLoCell_col h hr S a
    have hhi := S05_Lem5_06_insertMax_adjacentHiCell_col h hr S a
    unfold adjacentSameCol at *
    rw [hlo, hhi]
    exact hcol
  · intro hcol
    have hlo := S05_Lem5_06_insertMax_adjacentLoCell_col h hr S a
    have hhi := S05_Lem5_06_insertMax_adjacentHiCell_col h hr S a
    unfold adjacentSameCol at *
    rw [← hlo, ← hhi]
    exact hcol

/-- Lemma 5.4 content component: inserting the maximum box preserves the
content of every surviving entry. -/
theorem S05_Lem5_06_insertMax_entryContent_castSucc
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    entryContent S a =
      entryContent
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  have hcontent := S05_Lem5_06_deleteMax_entryContent h hr
    (deletedCornerCellOfOneBoxChildRow h hr)
    (deletedCornerCell_row h hr)
    (deletedCornerCell_col h hr)
    (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
    (insertMax_tableauMaxAt_deletedCorner h hr S)
    a
  have hdel := S05_Lem5_05_delete_insert h hr S
  simp [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow,
    hdel] at hcontent
  exact hcontent

/-- Lemma 5.4 coefficient component: one-box insertion preserves the axial
distance of every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_adjacentAxialDistance
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    adjacentAxialDistance S a =
      adjacentAxialDistance
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  unfold adjacentAxialDistance
  rw [S05_Lem5_06_insertMax_entryContent_castSucc h hr S (adjacentEntryHi a)]
  rw [S05_Lem5_06_insertMax_entryContent_castSucc h hr S (adjacentEntryLo a)]
  rw [S05_Lem5_06_castSucc_adjacentEntryHi a]
  rw [S05_Lem5_06_castSucc_adjacentEntryLo a]

/-- Lemma 5.4 coefficient component: one-box insertion preserves the diagonal
Young-adjacent coefficient for every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_youngAdjacentDiagCoeff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    youngAdjacentDiagCoeff S a =
      youngAdjacentDiagCoeff
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  rw [youngAdjacentDiagCoeff, youngAdjacentDiagCoeff,
    S05_Lem5_06_insertMax_adjacentAxialDistance h hr S a]

/-- Lemma 5.4 coefficient component: one-box insertion preserves the
off-diagonal Young-adjacent coefficient for every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_youngAdjacentOffCoeff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n) :
    youngAdjacentOffCoeff S a =
      youngAdjacentOffCoeff
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
          h hr S) (Fin.castSucc a) := by
  rw [youngAdjacentOffCoeff, youngAdjacentOffCoeff,
    S05_Lem5_06_insertMax_youngAdjacentDiagCoeff h hr S a]

/-- Reindexing helper: value swaps commute with adding a new maximum value
above the adjacent pair. -/
theorem S05_Lem5_06_adjacentSwapValue_castSucc
    {n : Nat} (a : Fin n) (x : Fin (n + 1)) :
    Fin.castSucc (adjacentSwapValue a x) =
      adjacentSwapValue (Fin.castSucc a) (Fin.castSucc x) := by
  by_cases hlo : x = adjacentEntryLo a
  · subst x
    rw [adjacentSwapValue_lo,
      S05_Lem5_06_castSucc_adjacentEntryHi,
      S05_Lem5_06_castSucc_adjacentEntryLo,
      adjacentSwapValue_lo]
  · by_cases hhi : x = adjacentEntryHi a
    · subst x
      rw [adjacentSwapValue_hi,
        S05_Lem5_06_castSucc_adjacentEntryLo,
        S05_Lem5_06_castSucc_adjacentEntryHi,
        adjacentSwapValue_hi]
    · have hlo' :
        Fin.castSucc x ≠ adjacentEntryLo (Fin.castSucc a) := by
        intro h
        apply hlo
        apply Fin.ext
        simpa [adjacentEntryLo] using congrArg Fin.val h
      have hhi' :
        Fin.castSucc x ≠ adjacentEntryHi (Fin.castSucc a) := by
        intro h
        apply hhi
        apply Fin.ext
        simpa [adjacentEntryHi] using congrArg Fin.val h
      rw [adjacentSwapValue_of_ne_lo_hi a hlo hhi,
        adjacentSwapValue_of_ne_lo_hi (Fin.castSucc a) hlo' hhi']

/-- Reindexing helper: an earlier adjacent value swap fixes the newly inserted
maximum value. -/
theorem S05_Lem5_06_adjacentSwapValue_last_castSucc
    {n : Nat} (a : Fin n) :
    adjacentSwapValue (Fin.castSucc a) (Fin.last (n + 1)) =
      Fin.last (n + 1) := by
  have hlo :
      Fin.last (n + 1) ≠ adjacentEntryLo (Fin.castSucc a) := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryLo] at hv
    omega
  have hhi :
      Fin.last (n + 1) ≠ adjacentEntryHi (Fin.castSucc a) := by
    intro h
    have hv := congrArg Fin.val h
    simp [adjacentEntryHi] at hv
    omega
  exact adjacentSwapValue_of_ne_lo_hi (Fin.castSucc a) hlo hhi

/-- Lemma 5.4 basis component: inserting the maximum box commutes with an
earlier adjacent tableau swap. -/
theorem S05_Lem5_06_insertMax_adjacentSwapTableau
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S : StandardYoungTableau mu) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow S a)
    (hcol_ne : ¬ adjacentSameCol S a) :
    S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr
        (adjacentSwapTableau S a hrow_ne hcol_ne)
      =
    adjacentSwapTableau
      (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
      (Fin.castSucc a)
      (by
        intro hp
        exact hrow_ne
          ((S05_Lem5_06_insertMax_adjacentSameRow_iff h hr S a).1 hp))
      (by
        intro hp
        exact hcol_ne
          ((S05_Lem5_06_insertMax_adjacentSameCol_iff h hr S a).1 hp)) := by
  apply standardYoungTableau_ext_entry
  intro u
  by_cases hu : u = deletedCornerCellOfOneBoxChildRow h hr
  · subst u
    change
      (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr
          (adjacentSwapTableau S a hrow_ne hcol_ne)).entry
        (deletedCornerCellOfOneBoxChildRow h hr)
        =
      adjacentSwapEntry
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
        (Fin.castSucc a)
        (deletedCornerCellOfOneBoxChildRow h hr)
    rw [S05_Lem5_05_insertMax_entry_deletedCorner,
      adjacentSwapEntry, S05_Lem5_05_insertMax_entry_deletedCorner,
      S05_Lem5_06_adjacentSwapValue_last_castSucc]
  · change
      (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr
          (adjacentSwapTableau S a hrow_ne hcol_ne)).entry u
        =
      adjacentSwapEntry
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
        (Fin.castSucc a) u
    let v : YoungCell mu :=
      (youngCellExceptEquivChildOfOneBoxChildRow h hr
        (deletedCornerCellOfOneBoxChildRow h hr)
        (deletedCornerCell_row h hr)
        (deletedCornerCell_col h hr)) ⟨u, hu⟩
    have hleft :
        (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr
            (adjacentSwapTableau S a hrow_ne hcol_ne)).entry u =
          Fin.castSucc ((adjacentSwapTableau S a hrow_ne hcol_ne).entry v) := by
      simpa [v] using
        S05_Lem5_05_insertMax_entry_ne_deletedCorner
          h hr (adjacentSwapTableau S a hrow_ne hcol_ne) u hu
    have hright :
        adjacentSwapEntry
            (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
            (Fin.castSucc a) u =
          adjacentSwapValue (Fin.castSucc a) (Fin.castSucc (S.entry v)) := by
      rw [adjacentSwapEntry]
      congr
      simpa [v] using
        S05_Lem5_05_insertMax_entry_ne_deletedCorner h hr S u hu
    rw [hleft, hright]
    simpa [adjacentSwapTableau, adjacentSwapEntry] using
      S05_Lem5_06_adjacentSwapValue_castSucc a (S.entry v)

/-- Lemma 5.4 basis component: one-box insertion is injective on standard
tableaux of the child shape. -/
theorem S05_Lem5_06_insertMax_injective
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    {S T : StandardYoungTableau mu}
    (hST :
      S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S =
        S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T) :
    S = T := by
  let e :=
    S05_Lem5_05_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow h hr
  have hsub : e.symm S = e.symm T := by
    apply Subtype.ext
    change
      insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S =
        insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T
    simpa [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow]
      using hST
  exact e.symm.injective hsub

/-- Lemma 5.4 matrix component: one-box insertion preserves the concrete
Young-adjacent matrix coefficients for every earlier adjacent pair. -/
theorem S05_Lem5_06_insertMax_youngAdjacentMatrixCoeff
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (S T : StandardYoungTableau mu) (a : Fin n) :
    youngAdjacentMatrixCoeff (Fin.castSucc a)
      (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
      (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
      =
    youngAdjacentMatrixCoeff a S T := by
  by_cases hrowT : adjacentSameRow T a
  · have hrowP :
        adjacentSameRow
          (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
          (Fin.castSucc a) :=
      (S05_Lem5_06_insertMax_adjacentSameRow_iff h hr T a).2 hrowT
    by_cases hST : S = T
    · subst S
      rw [youngAdjacentMatrixCoeff_sameRow_self
          (T := S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
            h hr T) (a := Fin.castSucc a) hrowP,
        youngAdjacentMatrixCoeff_sameRow_self (T := T) (a := a) hrowT]
    · have hPST :
          S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S ≠
            S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T := by
        intro hp
        exact hST (S05_Lem5_06_insertMax_injective h hr hp)
      rw [youngAdjacentMatrixCoeff_sameRow_ne (a := Fin.castSucc a) hrowP hPST,
        youngAdjacentMatrixCoeff_sameRow_ne (a := a) hrowT hST]
  · by_cases hcolT : adjacentSameCol T a
    · have hcolP :
          adjacentSameCol
            (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
            (Fin.castSucc a) :=
        (S05_Lem5_06_insertMax_adjacentSameCol_iff h hr T a).2 hcolT
      by_cases hST : S = T
      · subst S
        rw [youngAdjacentMatrixCoeff_sameCol_self
            (T := S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
              h hr T) (a := Fin.castSucc a) hcolP,
          youngAdjacentMatrixCoeff_sameCol_self (T := T) (a := a) hcolT]
      · have hPST :
            S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S ≠
              S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T := by
          intro hp
          exact hST (S05_Lem5_06_insertMax_injective h hr hp)
        rw [youngAdjacentMatrixCoeff_sameCol_ne (a := Fin.castSucc a) hcolP hPST,
          youngAdjacentMatrixCoeff_sameCol_ne (a := a) hcolT hST]
    · have hrowP :
          ¬ adjacentSameRow
            (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
            (Fin.castSucc a) := by
        intro hp
        exact hrowT
          ((S05_Lem5_06_insertMax_adjacentSameRow_iff h hr T a).1 hp)
      have hcolP :
          ¬ adjacentSameCol
            (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
            (Fin.castSucc a) := by
        intro hp
        exact hcolT
          ((S05_Lem5_06_insertMax_adjacentSameCol_iff h hr T a).1 hp)
      by_cases hST : S = T
      · subst S
        rw [youngAdjacentMatrixCoeff_swappable_self
            (T := S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
              h hr T) (a := Fin.castSucc a) hrowP hcolP,
          youngAdjacentMatrixCoeff_swappable_self (T := T) (a := a) hrowT hcolT,
          ← S05_Lem5_06_insertMax_youngAdjacentDiagCoeff h hr T a]
      · by_cases hSswap : S = adjacentSwapTableau T a hrowT hcolT
        · subst S
          have hswap :=
            S05_Lem5_06_insertMax_adjacentSwapTableau h hr T a hrowT hcolT
          rw [hswap,
            youngAdjacentMatrixCoeff_swappable_swap
              (T := S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
                h hr T) (a := Fin.castSucc a) hrowP hcolP,
            youngAdjacentMatrixCoeff_swappable_swap (T := T) (a := a)
              hrowT hcolT,
            ← S05_Lem5_06_insertMax_youngAdjacentOffCoeff h hr T a]
        · have hPST :
              S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S ≠
                S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T := by
            intro hp
            exact hST (S05_Lem5_06_insertMax_injective h hr hp)
          have hPswap :
              S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S ≠
                adjacentSwapTableau
                  (S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
                    h hr T)
                  (Fin.castSucc a) hrowP hcolP := by
            intro hp
            have hswap :=
              S05_Lem5_06_insertMax_adjacentSwapTableau h hr T a hrowT hcolT
            have hp' :
                S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
                    h hr S =
                  S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow
                    h hr (adjacentSwapTableau T a hrowT hcolT) := by
              exact hp.trans hswap.symm
            exact hSswap (S05_Lem5_06_insertMax_injective h hr hp')
          rw [youngAdjacentMatrixCoeff_swappable_other
              (a := Fin.castSucc a) hrowP hcolP hPST hPswap,
            youngAdjacentMatrixCoeff_swappable_other
              (a := a) hrowT hcolT hST hSswap]

/-- The parent-shape earlier adjacent operator restricted to the one-box
deletion fiber. -/
def S05_Lem5_06_deletionFiberYoungAdjacentOperator
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (a : Fin n)
    (f : S05_Lem5_05_OneBoxDeletionCoordinateSpace h hr) :
    S05_Lem5_05_OneBoxDeletionCoordinateSpace h hr :=
  fun S =>
    ∑ T : {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)},
      youngAdjacentMatrixCoeff (Fin.castSucc a) S.1 T.1 * f T

/-- Lemma 5.4 coordinate component: deleting the maximum entry intertwines
the child adjacent operator with the parent earlier-adjacent operator restricted
to the one-box deletion fiber. -/
theorem S05_Lem5_06_deletionCoordinateMap_youngAdjacentOperator_intertwines
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    {mu : YoungDiagram (n + 1)}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (a : Fin n)
    (f : S05_Lem5_05_OneBoxDeletionCoordinateSpace h hr) :
    youngAdjacentOperator a
        (S05_Lem5_05_deletionCoordinateMap h hr f)
      =
    S05_Lem5_05_deletionCoordinateMap h hr
      (S05_Lem5_06_deletionFiberYoungAdjacentOperator h hr a f) := by
  classical
  funext S
  let e :=
    S05_Lem5_05_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow h hr
  change
    (∑ T : StandardYoungTableau mu,
      youngAdjacentMatrixCoeff a S T * f (e.symm T)) =
    ∑ T : {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)},
      youngAdjacentMatrixCoeff (Fin.castSucc a) (e.symm S).1 T.1 * f T
  exact Fintype.sum_equiv e.symm
    (fun T : StandardYoungTableau mu =>
      youngAdjacentMatrixCoeff a S T * f (e.symm T))
    (fun T : {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} =>
      youngAdjacentMatrixCoeff (Fin.castSucc a) (e.symm S).1 T.1 * f T)
    (fun T => by
      have hcoeff :
          youngAdjacentMatrixCoeff a S T =
            youngAdjacentMatrixCoeff (Fin.castSucc a)
              (e.symm S).1 (e.symm T).1 := by
        change
          youngAdjacentMatrixCoeff a S T =
            youngAdjacentMatrixCoeff (Fin.castSucc a)
              (insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr S)
              (insertMaxAsStandardYoungTableauOfOneBoxChildRow h hr T)
        simpa [S05_Lem5_05_insertMaxAsStandardYoungTableauOfOneBoxChildRow] using
          (S05_Lem5_06_insertMax_youngAdjacentMatrixCoeff h hr S T a).symm
      rw [hcoeff])

/-- Lemma 5.4 coordinate component: one-box deletion intertwines the diagonal
content operator for every entry that survives the deletion. -/
theorem S05_Lem5_06_deletionCoordinateMap_diagonalContent_intertwines
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t)
    (a : Fin n)
    (f : S05_Lem5_05_OneBoxDeletionCoordinateSpace h hr) :
    jucysMurphyDiagonalOperator a
        (S05_Lem5_05_deletionCoordinateMap h hr f)
      =
    S05_Lem5_05_deletionCoordinateMap h hr
      (fun T => (entryContent T.1 (Fin.castSucc a) : ℝ) * f T) := by
  funext S
  let e := S05_Lem5_05_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow
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
    exact S05_Lem5_06_deleteMax_entryContent h hr
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
