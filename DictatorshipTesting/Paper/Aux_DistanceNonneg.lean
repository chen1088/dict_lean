import DictatorshipTesting.Paper.Defs

/-!
# Nonnegativity of squared distances
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared `L²` distance is nonnegative. -/
theorem l2DistSq_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) :
    0 ≤ l2DistSq F G := by
  unfold l2DistSq
  positivity

/-- Squared distance to `U₁` is nonnegative. -/
theorem l2DistSqToU1_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) :
    0 ≤ l2DistSqToU1 F := by
  unfold l2DistSqToU1
  apply Real.sInf_nonneg
  intro d hd
  rcases hd with ⟨G, _hG, rfl⟩
  exact l2DistSq_nonneg F G

end DictatorshipTesting
