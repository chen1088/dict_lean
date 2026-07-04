import DictatorshipTesting.Paper.Aux_YoungOrthogonal

/-!
Paper statement: Lemma 5.1 (`lem:young-adjacent-matrices`)
Title in paper: Adjacent transpositions in Young's basis.

Status: this file contains the first basis-level tableau facts needed for
Lemma 5.1.  The actual Young orthogonal representation matrices remain future
work.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.1 basis-level component: adjacent entries occupy distinct cells. -/
theorem S05_Lem5_01_adjacent_cells_distinct {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentLoCell T a ≠ adjacentHiCell T a := by
  exact adjacentLoCell_ne_hiCell T a

/-- Lemma 5.1 basis-level component: in a common row, the lower adjacent entry
is to the left. -/
theorem S05_Lem5_01_adjacent_col_lt_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentLoCell T a) <
      YoungCell.col (adjacentHiCell T a) := by
  exact adjacent_col_lt_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: in a common column, the lower adjacent
entry is above. -/
theorem S05_Lem5_01_adjacent_row_lt_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
      YoungCell.row (adjacentLoCell T a) <
        YoungCell.row (adjacentHiCell T a) := by
  exact adjacent_row_lt_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: same-row adjacent entries occupy
neighboring columns. -/
theorem S05_Lem5_01_adjacent_col_eq_succ_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.col (adjacentHiCell T a) =
      YoungCell.col (adjacentLoCell T a) + 1 := by
  exact adjacent_col_eq_succ_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: same-column adjacent entries occupy
neighboring rows. -/
theorem S05_Lem5_01_adjacent_row_eq_succ_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.row (adjacentHiCell T a) =
      YoungCell.row (adjacentLoCell T a) + 1 := by
  exact adjacent_row_eq_succ_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: same-row adjacent contents differ by `+1`. -/
theorem S05_Lem5_01_adjacent_content_hi_eq_lo_add_one_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow :
      YoungCell.row (adjacentLoCell T a) =
        YoungCell.row (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) + 1 := by
  exact adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow

/-- Lemma 5.1 basis-level component: same-column adjacent contents differ by `-1`. -/
theorem S05_Lem5_01_adjacent_content_hi_eq_lo_sub_one_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol :
      YoungCell.col (adjacentLoCell T a) =
        YoungCell.col (adjacentHiCell T a)) :
    YoungCell.content (adjacentHiCell T a) =
      YoungCell.content (adjacentLoCell T a) - 1 := by
  exact adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol

/-- Lemma 5.1 basis-level component: the adjacent swap sends the lower
adjacent-entry cell to the upper adjacent value. -/
theorem S05_Lem5_01_adjacentSwapEntry_loCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentLoCell T a) = adjacentEntryHi a := by
  exact adjacentSwapEntry_loCell T a

/-- Lemma 5.1 basis-level component: the adjacent swap sends the upper
adjacent-entry cell to the lower adjacent value. -/
theorem S05_Lem5_01_adjacentSwapEntry_hiCell {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSwapEntry T a (adjacentHiCell T a) = adjacentEntryLo a := by
  exact adjacentSwapEntry_hiCell T a

/-- Lemma 5.1 basis-level component: swapping two adjacent values is bijective
on the cell set. -/
theorem S05_Lem5_01_adjacentSwapEntry_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Function.Bijective (adjacentSwapEntry T a) := by
  exact adjacentSwapEntry_bijective T a

/-- Lemma 5.1 basis-level component: if adjacent entries are in different rows
and columns, swapping their values gives another standard tableau. -/
noncomputable def S05_Lem5_01_adjacentSwapTableau {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    StandardYoungTableau lam :=
  adjacentSwapTableau T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after swapping adjacent values, the lower
entry lies in the old upper cell. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryLo a) =
      adjacentHiCell T a := by
  exact adjacentSwapTableau_cell_lo T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after swapping adjacent values, the upper
entry lies in the old lower cell. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryHi a) =
      adjacentLoCell T a := by
  exact adjacentSwapTableau_cell_hi T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: non-adjacent entries keep their cells after
the adjacent swap. -/
theorem S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi {n : Nat}
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
    cellOfEntry (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      cellOfEntry T b := by
  exact adjacentSwapTableau_cell_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.1 basis-level component: after the adjacent swap, the lower entry
has the old upper entry's content. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_lo {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryLo a) =
      entryContent T (adjacentEntryHi a) := by
  exact adjacentSwapTableau_entryContent_lo T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: after the adjacent swap, the upper entry
has the old lower entry's content. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_hi {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne :
      YoungCell.row (adjacentLoCell T a) ≠
        YoungCell.row (adjacentHiCell T a))
    (hcol_ne :
      YoungCell.col (adjacentLoCell T a) ≠
        YoungCell.col (adjacentHiCell T a)) :
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) (adjacentEntryHi a) =
      entryContent T (adjacentEntryLo a) := by
  exact adjacentSwapTableau_entryContent_hi T a hrow_ne hcol_ne

/-- Lemma 5.1 basis-level component: non-adjacent entry contents are preserved
by the adjacent swap. -/
theorem S05_Lem5_01_adjacentSwapTableau_entryContent_of_ne_lo_hi {n : Nat}
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
    entryContent (adjacentSwapTableau T a hrow_ne hcol_ne) b =
      entryContent T b := by
  exact adjacentSwapTableau_entryContent_of_ne_lo_hi T a hrow_ne hcol_ne hblo hbhi

/-- Lemma 5.1 coefficient component: the axial distance is `1` in the
same-row case. -/
theorem S05_Lem5_01_adjacentAxialDistance_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    adjacentAxialDistance T a = 1 := by
  exact adjacentAxialDistance_sameRow T a hrow

/-- Lemma 5.1 coefficient component: the axial distance is `-1` in the
same-column case. -/
theorem S05_Lem5_01_adjacentAxialDistance_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    adjacentAxialDistance T a = -1 := by
  exact adjacentAxialDistance_sameCol T a hcol

/-- Lemma 5.1 coefficient component: swapping a swappable adjacent pair negates
the axial distance. -/
theorem S05_Lem5_01_adjacentAxialDistance_swap_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - adjacentAxialDistance T a := by
  exact adjacentAxialDistance_swap_neg T a hrow_ne hcol_ne

/-- Lemma 5.1 coefficient component: the diagonal coefficient is `1` in the
same-row case. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentDiagCoeff T a = 1 := by
  exact youngAdjacentDiagCoeff_sameRow T a hrow

/-- Lemma 5.1 coefficient component: the diagonal coefficient is `-1` in the
same-column case. -/
theorem S05_Lem5_01_youngAdjacentDiagCoeff_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a = -1 := by
  exact youngAdjacentDiagCoeff_sameCol T a hcol

/-- Lemma 5.1 matrix-coefficient component: same-row adjacent pairs act
diagonally with coefficient `1` on their tableau. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameRow_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a T T = 1 := by
  exact youngAdjacentMatrixCoeff_sameRow_self T a hrow

/-- Lemma 5.1 matrix-coefficient component: same-row adjacent pairs have no
off-diagonal support. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameRow_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow : adjacentSameRow T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_sameRow_ne a hrow hST

/-- Lemma 5.1 matrix-coefficient component: same-column adjacent pairs act
diagonally with coefficient `-1` on their tableau. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameCol_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = -1 := by
  exact youngAdjacentMatrixCoeff_sameCol_self T a hcol

/-- Lemma 5.1 matrix-coefficient component: same-column adjacent pairs have no
off-diagonal support. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_sameCol_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hcol : adjacentSameCol T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_sameCol_ne a hcol hST

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, the
coefficient at `T` is the diagonal axial coefficient. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = youngAdjacentDiagCoeff T a := by
  exact youngAdjacentMatrixCoeff_swappable_self T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, the
coefficient at the swapped tableau is the off-diagonal axial coefficient. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentOffCoeff T a := by
  exact youngAdjacentMatrixCoeff_swappable_swap T a hrow_ne hcol_ne

/-- Lemma 5.1 matrix-coefficient component: in the swappable case, all other
tableaux have coefficient zero. -/
theorem S05_Lem5_01_youngAdjacentMatrixCoeff_swappable_other {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  exact youngAdjacentMatrixCoeff_swappable_other a hrow_ne hcol_ne hST hSswap

end DictatorshipTesting
