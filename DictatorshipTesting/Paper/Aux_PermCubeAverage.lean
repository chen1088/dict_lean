import DictatorshipTesting.Paper.Aux_OrderedMatchingTauMul

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Lem4_06_LocalHighDegreeErrorFormula`
- `DictatorshipTesting.Paper.S04_Lem4_07_PMPerpendicular`
- `DictatorshipTesting.Paper.S04_Prop4_12_SquareEnergyControlsGlobalDegree`
-/


/-!
# Averaging over matching-cube translates

These are finite-sum bookkeeping lemmas for replacing averages over translated
matching cubes by the global permutation average.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A finite sum over permutations is invariant under right multiplication. -/
theorem sum_perm_mul_right {α : Type*} [Fintype α] [DecidableEq α]
    (a : Perm α) (f : Perm α → ℝ) :
    (∑ π : Perm α, f (π * a)) = ∑ π : Perm α, f π := by
  simpa using (Equiv.sum_comp (Equiv.mulRight a) f)

/-- Averaging a global function over all matching-cube translates gives the
global permutation average back. -/
theorem sum_perm_cube_right_tau_div_card {α : Type*} [Fintype α]
    [DecidableEq α] (M : OrderedMatching α) (e : Perm α → ℝ) :
    (∑ π : Perm α,
        (∑ x : Cube M.edgeCount, e (π * M.tau x)) /
          (Fintype.card (Cube M.edgeCount) : ℝ)) =
      ∑ π : Perm α, e π := by
  classical
  let C : ℝ := Fintype.card (Cube M.edgeCount)
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast
      (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Cube M.edgeCount)))
  calc
    (∑ π : Perm α,
        (∑ x : Cube M.edgeCount, e (π * M.tau x)) /
          (Fintype.card (Cube M.edgeCount) : ℝ))
        =
        (∑ π : Perm α, ∑ x : Cube M.edgeCount, e (π * M.tau x)) / C := by
          dsimp [C]
          rw [Finset.sum_div]
    _ =
        (∑ x : Cube M.edgeCount, ∑ π : Perm α, e (π * M.tau x)) / C := by
          rw [Finset.sum_comm]
    _ =
        (∑ x : Cube M.edgeCount, ∑ π : Perm α, e π) / C := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          rw [sum_perm_mul_right]
    _ =
        (C * ∑ π : Perm α, e π) / C := by
          congr 1
          simp [C, nsmul_eq_mul]
    _ = ∑ π : Perm α, e π := by
          field_simp [hC_ne]

end DictatorshipTesting
