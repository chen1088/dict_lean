import DictatorshipTesting.Paper.Aux_YoungAdjacentEntries
import DictatorshipTesting.Paper.Aux_SpectralBridgeDimensionParam

/-!
Elementary coordinate-space objects for the tableau-basis side of the rewritten
Section 5 proof.  This file deliberately stops before any Specht-module or
Schur-lemma assertions: the objects here are just finite functions on standard
Young tableaux, their coordinate basis, and the Euclidean dot product.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

local instance standardYoungTableauDecidableEq {n : Nat} {lam : YoungDiagram n} :
    DecidableEq (StandardYoungTableau lam) :=
  Classical.decEq _

/-- The real coordinate space with standard tableaux of shape `lam` as basis. -/
abbrev TableauSpace {n : Nat} (lam : YoungDiagram n) :=
  StandardYoungTableau lam -> ℝ

/-- The coordinate basis vector indexed by one standard tableau. -/
def tableauBasisVec {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) : TableauSpace lam :=
  fun S => if S = T then 1 else 0

/-- The Euclidean dot product in the tableau coordinate basis. -/
def tableauInner {n : Nat} {lam : YoungDiagram n}
    (f g : TableauSpace lam) : ℝ :=
  ∑ T : StandardYoungTableau lam, f T * g T

@[simp] theorem tableauBasisVec_self {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :
    tableauBasisVec T T = 1 := by
  simp [tableauBasisVec]

theorem tableauBasisVec_ne {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (h : S ≠ T) :
    tableauBasisVec T S = 0 := by
  simp [tableauBasisVec, h]

@[simp] theorem tableauInner_basis_basis_self {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :
    tableauInner (tableauBasisVec T) (tableauBasisVec T) = 1 := by
  classical
  rw [tableauInner]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro S hS
    simp [tableauBasisVec, hS]

theorem tableauInner_basis_basis_ne {n : Nat} {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (h : S ≠ T) :
    tableauInner (tableauBasisVec S) (tableauBasisVec T) = 0 := by
  classical
  rw [tableauInner]
  apply Finset.sum_eq_zero
  intro U _
  by_cases hUS : U = S
  · subst U
    simp [tableauBasisVec, h]
  · simp [tableauBasisVec, hUS]

theorem tableauInner_basis_basis_eq_ite {n : Nat} {lam : YoungDiagram n}
    (S T : StandardYoungTableau lam) :
    tableauInner (tableauBasisVec S) (tableauBasisVec T) =
      if S = T then 1 else 0 := by
  by_cases h : S = T
  · subst T
    simp
  · simp [h, tableauInner_basis_basis_ne h]

/-- The adjacent entries indexed by `a` occupy a common row. -/
def adjacentSameRow {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Prop :=
  YoungCell.row (adjacentLoCell T a) =
    YoungCell.row (adjacentHiCell T a)

/-- The adjacent entries indexed by `a` occupy a common column. -/
def adjacentSameCol {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Prop :=
  YoungCell.col (adjacentLoCell T a) =
    YoungCell.col (adjacentHiCell T a)

local instance adjacentSameRowDecidable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameRow T a) := by
  unfold adjacentSameRow
  infer_instance

local instance adjacentSameColDecidable {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameCol T a) := by
  unfold adjacentSameCol
  infer_instance

/-- Axial distance between the cells of adjacent entries `a` and `a+1`. -/
def adjacentAxialDistance {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : Int :=
  entryContent T (adjacentEntryHi a) -
    entryContent T (adjacentEntryLo a)

theorem adjacentAxialDistance_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    adjacentAxialDistance T a = 1 := by
  have hcontent :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) + 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, adjacentSameRow] using
      adjacent_content_hi_eq_lo_add_one_of_sameRow T a hrow
  unfold adjacentAxialDistance
  omega

theorem adjacentAxialDistance_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    adjacentAxialDistance T a = -1 := by
  have hcontent :
      entryContent T (adjacentEntryHi a) =
        entryContent T (adjacentEntryLo a) - 1 := by
    simpa [entryContent, adjacentHiCell, adjacentLoCell, adjacentSameCol] using
      adjacent_content_hi_eq_lo_sub_one_of_sameCol T a hcol
  unfold adjacentAxialDistance
  omega

theorem adjacentAxialDistance_swap_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentAxialDistance (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - adjacentAxialDistance T a := by
  unfold adjacentAxialDistance
  rw [adjacentSwapTableau_entryContent_hi,
    adjacentSwapTableau_entryContent_lo]
  omega

/-- Diagonal coefficient in Young's adjacent-transposition formula. -/
noncomputable def youngAdjacentDiagCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : ℝ :=
  (adjacentAxialDistance T a : ℝ)⁻¹

/-- Off-diagonal coefficient in Young's adjacent-transposition formula. -/
noncomputable def youngAdjacentOffCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) : ℝ :=
  Real.sqrt (1 - youngAdjacentDiagCoeff T a ^ 2)

theorem youngAdjacentDiagCoeff_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentDiagCoeff T a = 1 := by
  rw [youngAdjacentDiagCoeff, adjacentAxialDistance_sameRow T a hrow]
  norm_num

theorem youngAdjacentDiagCoeff_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentDiagCoeff T a = -1 := by
  rw [youngAdjacentDiagCoeff, adjacentAxialDistance_sameCol T a hcol]
  norm_num

theorem youngAdjacentDiagCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentDiagCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      - youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_swap_neg T a hrow_ne hcol_ne,
    youngAdjacentDiagCoeff]
  simp

theorem youngAdjacentOffCoeff_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOffCoeff (adjacentSwapTableau T a hrow_ne hcol_ne) a =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOffCoeff, youngAdjacentDiagCoeff_swap T a hrow_ne hcol_ne,
    youngAdjacentOffCoeff]
  ring_nf

theorem youngAdjacentOffCoeff_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    0 ≤ youngAdjacentOffCoeff T a := by
  exact Real.sqrt_nonneg _

theorem youngAdjacentOffCoeff_sq_of_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h :
      0 ≤ 1 - youngAdjacentDiagCoeff T a ^ 2) :
    youngAdjacentOffCoeff T a ^ 2 =
      1 - youngAdjacentDiagCoeff T a ^ 2 := by
  rw [youngAdjacentOffCoeff, Real.sq_sqrt h]

theorem youngAdjacentCoeff_sq_sum_of_nonneg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (h :
      0 ≤ 1 - youngAdjacentDiagCoeff T a ^ 2) :
    youngAdjacentDiagCoeff T a ^ 2 +
        youngAdjacentOffCoeff T a ^ 2 = 1 := by
  rw [youngAdjacentOffCoeff_sq_of_nonneg T a h]
  ring

theorem not_adjacentSameRow_of_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    ¬ adjacentSameRow T a := by
  intro hrow
  exact adjacentLoCell_ne_hiCell T a
    (YoungCell.ext_row_col hrow hcol)

theorem not_adjacentSameCol_of_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    ¬ adjacentSameCol T a := by
  intro hcol
  exact adjacentLoCell_ne_hiCell T a
    (YoungCell.ext_row_col hrow hcol)

theorem adjacentSwapTableau_ne_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSwapTableau T a hrow_ne hcol_ne ≠ T := by
  intro h
  have hentry :=
    congrArg (fun U : StandardYoungTableau lam =>
      U.entry (adjacentLoCell T a)) h
  change adjacentSwapEntry T a (adjacentLoCell T a) =
    T.entry (adjacentLoCell T a) at hentry
  rw [adjacentSwapEntry_loCell, entry_adjacentLoCell] at hentry
  exact adjacentEntryLo_ne_hi a hentry.symm

theorem adjacentSameRow_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a ↔
      adjacentSameRow T a := by
  unfold adjacentSameRow adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo, adjacentSwapTableau_cell_hi]
  exact eq_comm

theorem adjacentSameCol_swap_iff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a ↔
      adjacentSameCol T a := by
  unfold adjacentSameCol adjacentLoCell adjacentHiCell
  rw [adjacentSwapTableau_cell_lo, adjacentSwapTableau_cell_hi]
  exact eq_comm

theorem not_adjacentSameRow_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    ¬ adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a := by
  intro h
  exact hrow_ne ((adjacentSameRow_swap_iff T a hrow_ne hcol_ne).1 h)

theorem not_adjacentSameCol_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    ¬ adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a := by
  intro h
  exact hcol_ne ((adjacentSameCol_swap_iff T a hrow_ne hcol_ne).1 h)

theorem adjacentSwapTableau_involutive {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hrow_ne' :
      ¬ adjacentSameRow (adjacentSwapTableau T a hrow_ne hcol_ne) a)
    (hcol_ne' :
      ¬ adjacentSameCol (adjacentSwapTableau T a hrow_ne hcol_ne) a) :
    adjacentSwapTableau
        (adjacentSwapTableau T a hrow_ne hcol_ne) a hrow_ne' hcol_ne' =
      T := by
  apply standardYoungTableau_ext_entry
  intro u
  simp [adjacentSwapTableau, adjacentSwapEntry, adjacentSwapValue_involutive]

/-- Matrix coefficient of the Young adjacent-transposition formula in the
standard tableau basis.  This is only the concrete coefficient model, not yet a
claim that it realizes a symmetric-group representation. -/
noncomputable def youngAdjacentMatrixCoeff {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) : ℝ :=
  if hrow : adjacentSameRow T a then
    if S = T then 1 else 0
  else if hcol : adjacentSameCol T a then
    if S = T then -1 else 0
  else
    if S = T then youngAdjacentDiagCoeff T a
    else if S = adjacentSwapTableau T a hrow hcol then
      youngAdjacentOffCoeff T a
    else 0

theorem youngAdjacentMatrixCoeff_sameRow_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentMatrixCoeff a T T = 1 := by
  simp [youngAdjacentMatrixCoeff, hrow]

theorem youngAdjacentMatrixCoeff_sameRow_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow : adjacentSameRow T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  simp [youngAdjacentMatrixCoeff, hrow, hST]

theorem youngAdjacentMatrixCoeff_sameCol_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = -1 := by
  have hrow_ne := not_adjacentSameRow_of_sameCol T a hcol
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol]

theorem youngAdjacentMatrixCoeff_sameCol_ne {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hcol : adjacentSameCol T a) (hST : S ≠ T) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  have hrow_ne := not_adjacentSameRow_of_sameCol T a hcol
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol, hST]

theorem youngAdjacentMatrixCoeff_swappable_self {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T T = youngAdjacentDiagCoeff T a := by
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne]

theorem youngAdjacentMatrixCoeff_swappable_swap {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a
        (adjacentSwapTableau T a hrow_ne hcol_ne) T =
      youngAdjacentOffCoeff T a := by
  have hswap_ne := adjacentSwapTableau_ne_self T a hrow_ne hcol_ne
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne, hswap_ne]

theorem youngAdjacentMatrixCoeff_swappable_swap_symm {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentMatrixCoeff a T
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  let T' := adjacentSwapTableau T a hrow_ne hcol_ne
  have hrow_ne' : ¬ adjacentSameRow T' a := by
    simpa [T'] using not_adjacentSameRow_swap T a hrow_ne hcol_ne
  have hcol_ne' : ¬ adjacentSameCol T' a := by
    simpa [T'] using not_adjacentSameCol_swap T a hrow_ne hcol_ne
  have h :=
    youngAdjacentMatrixCoeff_swappable_swap T' a hrow_ne' hcol_ne'
  have hinv :
      adjacentSwapTableau T' a hrow_ne' hcol_ne' = T := by
    simpa [T'] using
      adjacentSwapTableau_involutive T a hrow_ne hcol_ne hrow_ne' hcol_ne'
  have hoff :
      youngAdjacentOffCoeff T' a = youngAdjacentOffCoeff T a := by
    simpa [T'] using youngAdjacentOffCoeff_swap T a hrow_ne hcol_ne
  simpa [T', hinv, hoff] using h

theorem youngAdjacentMatrixCoeff_swappable_other {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentMatrixCoeff a S T = 0 := by
  simp [youngAdjacentMatrixCoeff, hrow_ne, hcol_ne, hST, hSswap]

/-- The adjacent-transposition matrix on the tableau coordinate space.  This is
the explicit Young-orthogonal matrix model on a single shape. -/
noncomputable def youngAdjacentOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} (a : Fin n) :
    TableauSpace lam -> TableauSpace lam :=
  fun f S =>
    ∑ T : StandardYoungTableau lam, youngAdjacentMatrixCoeff a S T * f T

theorem youngAdjacentOperator_basis_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (S T : StandardYoungTableau lam) :
    youngAdjacentOperator a (tableauBasisVec T) S =
      youngAdjacentMatrixCoeff a S T := by
  classical
  rw [youngAdjacentOperator]
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro U hU
    simp [tableauBasisVec, hU]

theorem youngAdjacentOperator_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a (tableauBasisVec T) = tableauBasisVec T := by
  funext S
  by_cases hST : S = T
  · subst S
    rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameRow_self]
    · simp
    · exact hrow
  · rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameRow_ne a hrow hST,
      tableauBasisVec_ne hST]

theorem youngAdjacentOperator_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) =
      fun S => - tableauBasisVec T S := by
  funext S
  by_cases hST : S = T
  · subst S
    rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameCol_self]
    · simp
    · exact hcol
  · rw [youngAdjacentOperator_basis_value,
      youngAdjacentMatrixCoeff_sameCol_ne a hcol hST,
      tableauBasisVec_ne hST]
    simp

theorem youngAdjacentOperator_basis_swappable_self_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_self T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_basis_swappable_swap_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a (tableauBasisVec T)
        (adjacentSwapTableau T a hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_swap T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_basis_swappable_swap_symm_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a) :
    youngAdjacentOperator a
        (tableauBasisVec (adjacentSwapTableau T a hrow_ne hcol_ne)) T =
      youngAdjacentOffCoeff T a := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_swap_symm T a hrow_ne hcol_ne]

theorem youngAdjacentOperator_basis_swappable_other_value {n : Nat}
    {lam : YoungDiagram (n + 1)}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hrow_ne : ¬ adjacentSameRow T a)
    (hcol_ne : ¬ adjacentSameCol T a)
    (hST : S ≠ T)
    (hSswap : S ≠ adjacentSwapTableau T a hrow_ne hcol_ne) :
    youngAdjacentOperator a (tableauBasisVec T) S = 0 := by
  rw [youngAdjacentOperator_basis_value,
    youngAdjacentMatrixCoeff_swappable_other a hrow_ne hcol_ne hST hSswap]

theorem youngAdjacentOperator_neg {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    youngAdjacentOperator a (fun S => - f S) =
      fun S => - youngAdjacentOperator a f S := by
  funext S
  unfold youngAdjacentOperator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem youngAdjacentOperator_sq_basis_sameRow {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hrow : adjacentSameRow T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  rw [youngAdjacentOperator_basis_sameRow T a hrow,
    youngAdjacentOperator_basis_sameRow T a hrow]

theorem youngAdjacentOperator_sq_basis_sameCol {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (hcol : adjacentSameCol T a) :
    youngAdjacentOperator a
        (youngAdjacentOperator a (tableauBasisVec T)) =
      tableauBasisVec T := by
  rw [youngAdjacentOperator_basis_sameCol T a hcol,
    youngAdjacentOperator_neg,
    youngAdjacentOperator_basis_sameCol T a hcol]
  funext S
  simp

/-- The diagonal content operator in the tableau coordinate basis. -/
noncomputable def jucysMurphyDiagonalOperator {n : Nat}
    {lam : YoungDiagram n} (a : Fin n) :
    TableauSpace lam -> TableauSpace lam :=
  fun f T => (entryContent T a : ℝ) * f T

theorem jucysMurphyDiagonalOperator_basis_self {n : Nat}
    {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) T =
      (entryContent T a : ℝ) := by
  simp [jucysMurphyDiagonalOperator, tableauBasisVec]

theorem jucysMurphyDiagonalOperator_basis_ne {n : Nat}
    {lam : YoungDiagram n}
    {S T : StandardYoungTableau lam} (a : Fin n)
    (hST : S ≠ T) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) S = 0 := by
  simp [jucysMurphyDiagonalOperator, tableauBasisVec, hST]

theorem jucysMurphyDiagonalOperator_basis_eigen {n : Nat}
    {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a (tableauBasisVec T) =
      fun S => (entryContent T a : ℝ) * tableauBasisVec T S := by
  funext S
  by_cases hST : S = T
  · subst S
    simp [jucysMurphyDiagonalOperator, tableauBasisVec]
  · simp [jucysMurphyDiagonalOperator, tableauBasisVec, hST]

end DictatorshipTesting
