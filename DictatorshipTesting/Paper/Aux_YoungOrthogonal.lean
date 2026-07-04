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

end DictatorshipTesting
