import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis

/-!
Paper statement: Lemma 5.2 (`lem:jucys-murphy-eigenbasis`)
Title in paper: Diagonal content eigenspaces.

Status: this file records the basis-level content API used by the future
Jucys--Murphy statement.  The actual operator/eigenbasis theorem remains future
work in the Specht-module/tableau representation layer.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.2 basis-level vocabulary: content of a tableau cell. -/
def S05_Lem5_02_cellContent {n : Nat} {lam : YoungDiagram n}
    (u : YoungCell lam) : Int :=
  YoungCell.content u

/-- Lemma 5.2 basis-level vocabulary: content of the cell containing an entry. -/
noncomputable def S05_Lem5_02_entryContent {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T a

/-- Basis-level content sequence of a standard tableau, indexed by entries. -/
noncomputable def tableauContentSequence {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : Fin n → Int :=
  fun a => entryContent T a

/-- Lemma 5.2 basis-level vocabulary: content sequence of a standard tableau. -/
noncomputable def S05_Lem5_02_tableauContentSequence {n : Nat}
    {lam : YoungDiagram n} (T : StandardYoungTableau lam) : Fin n → Int :=
  tableauContentSequence T

/-- Basis-level component: after swapping adjacent values, the lower entry gets
the old upper entry's content. -/
theorem tableauContentSequence_adjacentSwap_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryLo a) =
      tableauContentSequence T (adjacentEntryHi a) := by
  exact adjacentSwapTableau_entryContent_lo T a hrow_ne hcol_ne

/-- Basis-level component: after swapping adjacent values, the upper entry gets
the old lower entry's content. -/
theorem tableauContentSequence_adjacentSwap_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryHi a) =
      tableauContentSequence T (adjacentEntryLo a) := by
  exact adjacentSwapTableau_entryContent_hi T a hrow_ne hcol_ne

/-- Basis-level component: adjacent swaps preserve all non-adjacent content
values. -/
theorem tableauContentSequence_adjacentSwap_of_ne_lo_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    {b : Fin (n + 1)}
    (hblo : b ≠ adjacentEntryLo a)
    (hbhi : b ≠ adjacentEntryHi a) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      tableauContentSequence T b := by
  exact adjacentSwapTableau_entryContent_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.2 basis-level component: after swapping adjacent values, the lower
entry gets the old upper entry's content. -/
theorem S05_Lem5_02_tableauContentSequence_adjacentSwap_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryLo a) =
      tableauContentSequence T (adjacentEntryHi a) := by
  exact tableauContentSequence_adjacentSwap_lo T a hrow_ne hcol_ne

/-- Lemma 5.2 basis-level component: after swapping adjacent values, the upper
entry gets the old lower entry's content. -/
theorem S05_Lem5_02_tableauContentSequence_adjacentSwap_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne)
        (adjacentEntryHi a) =
      tableauContentSequence T (adjacentEntryLo a) := by
  exact tableauContentSequence_adjacentSwap_hi T a hrow_ne hcol_ne

/-- Lemma 5.2 basis-level component: adjacent swaps preserve non-adjacent
content-sequence values. -/
theorem S05_Lem5_02_tableauContentSequence_adjacentSwap_of_ne_lo_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a))
    {b : Fin (n + 1)}
    (hblo : b ≠ adjacentEntryLo a)
    (hbhi : b ≠ adjacentEntryHi a) :
    tableauContentSequence (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      tableauContentSequence T b := by
  exact tableauContentSequence_adjacentSwap_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.2 basis-level component: adjacent entry contents differ by `+1`
in the same-row case. -/
theorem S05_Lem5_02_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) + 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.2 basis-level component: symmetric form of the same-row adjacent
content difference. -/
theorem S05_Lem5_02_entryContent_adjacent_lo_eq_hi_sub_one_of_sameRow
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) - 1 := by
  have h :=
    S05_Lem5_02_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow T a hrow
  omega

/-- Lemma 5.2 basis-level component: adjacent entry contents differ by `-1`
in the same-column case. -/
theorem S05_Lem5_02_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) - 1 := by
  simpa [entryContent, adjacentHiCell, adjacentLoCell]
    using adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

/-- Lemma 5.2 basis-level component: symmetric form of the same-column adjacent
content difference. -/
theorem S05_Lem5_02_entryContent_adjacent_lo_eq_hi_add_one_of_sameCol
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    entryContent T (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) + 1 := by
  have h :=
    S05_Lem5_02_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol T a hcol
  omega

/-- Lemma 5.2 coordinate component: the diagonal content operator has
eigenvalue equal to the entry content on the matching tableau basis vector. -/
theorem S05_Lem5_02_jucysMurphyDiagonalOperator_basis_self
    {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) T =
      (entryContent T a : ℝ) := by
  exact jucysMurphyDiagonalOperator_basis_self T a

/-- Lemma 5.2 coordinate component: the diagonal content operator has zero
coordinate on every other tableau basis vector. -/
theorem S05_Lem5_02_jucysMurphyDiagonalOperator_basis_ne
    {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hST : S ≠ T) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) S = 0 := by
  exact jucysMurphyDiagonalOperator_basis_ne a hST

/-- Lemma 5.2 coordinate component: each tableau basis vector is an eigenvector
of the diagonal content operator. -/
theorem S05_Lem5_02_jucysMurphyDiagonalOperator_basis_eigen
    {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) =
      fun S => (entryContent T a : ℝ) * tableauBasisVec T S := by
  exact jucysMurphyDiagonalOperator_basis_eigen T a

end DictatorshipTesting
