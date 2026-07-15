import AlgebraicLibrary.Young.OrthogonalRepresentation

/-!
# Traces in tableau coordinates

This module computes operator traces in the standard-tableau coordinate basis.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicLibrary

/-- Trace of an operator on a tableau coordinate space, computed in the
standard-tableau basis. -/
def tableauOperatorTrace {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam → TableauSpace lam) : ℝ :=
  ∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T

/-- A scalar operator on the tableau basis has trace equal to the tableau
dimension times its scalar. -/
theorem tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam → TableauSpace lam) (c : ℝ)
    (hscalar :
      ∀ T : StandardYoungTableau lam,
        op (tableauBasisVec T) =
          fun U => c * tableauBasisVec T U) :
    tableauOperatorTrace op = tableauDim lam * c := by
  classical
  unfold tableauOperatorTrace
  calc
    (∑ T : StandardYoungTableau lam, op (tableauBasisVec T) T) =
        ∑ _T : StandardYoungTableau lam, c := by
      apply Finset.sum_congr rfl
      intro T _hT
      rw [hscalar T]
      simp [tableauBasisVec]
    _ = (Fintype.card (StandardYoungTableau lam) : ℝ) * c := by
      simp
    _ = tableauDim lam * c := by
      rw [tableauDim, tableauDimNat_eq_card]

/-- If the tableau dimension is nonzero, the scalar of a scalar-on-basis
operator is its trace divided by the tableau dimension. -/
theorem scalar_eq_tableauOperatorTrace_div_tableauDim
    {n : Nat} {lam : YoungDiagram n}
    (op : TableauSpace lam → TableauSpace lam) (c : ℝ)
    (hdim : tableauDim lam ≠ 0)
    (hscalar :
      ∀ T : StandardYoungTableau lam,
        op (tableauBasisVec T) =
          fun U => c * tableauBasisVec T U) :
    c = tableauOperatorTrace op / tableauDim lam := by
  rw [tableauOperatorTrace_eq_tableauDim_mul_of_scalar_on_basis op c hscalar]
  field_simp

end AlgebraicLibrary
