import DictatorshipTesting.Paper.Defs.S04_Def4_02b_MatchingLocalProjectionError
import DictatorshipTesting.Paper.S04_Int_CubeLowDegreeError
import DictatorshipTesting.Paper.S04_Int_MatchingLocalProjection
import DictatorshipTesting.Paper.S04_Int_PermCubeAverage

/-
Direct reverse imports:
- None.
-/


/-!
# Internal local high-degree error formula

This proof supplies part (b) of Proposition 4.3.
-/

namespace DictatorshipTesting

/-- The projection error equals the average local high-degree Fourier energy. -/
theorem matchingLocalProjection_error_formula {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M = matchingLocalHighDegreeEnergy F M := by
  classical
  unfold matchingLocalProjectionError matchingLocalHighDegreeEnergy l2DistSq
  congr 1
  symm
  calc
    (∑ π : Perm α,
        cubeHighDegreeEnergy (fun x : Cube M.edgeCount => F (π * M.tau x)))
        =
        ∑ π : Perm α,
          cubeExpectation
            (fun x : Cube M.edgeCount =>
              (F (π * M.tau x) -
                cubeLowDegreeOnePart
                  (fun y : Cube M.edgeCount => F (π * M.tau y)) x) ^
                (2 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro π _hπ
          rw [← cubeExpectation_sq_sub_cubeLowDegreeOnePart_eq_highDegreeEnergy]
    _ =
        ∑ π : Perm α,
          (∑ x : Cube M.edgeCount,
              (F (π * M.tau x) -
                cubeLowDegreeOnePart
                  (fun y : Cube M.edgeCount => F (π * M.tau y)) x) ^
                (2 : ℕ)) /
            (Fintype.card (Cube M.edgeCount) : ℝ) := by
          rfl
    _ =
        ∑ π : Perm α,
          (∑ x : Cube M.edgeCount,
              (F (π * M.tau x) -
                matchingLocalProjection M F (π * M.tau x)) ^ (2 : ℕ)) /
            (Fintype.card (Cube M.edgeCount) : ℝ) := by
          apply Finset.sum_congr rfl
          intro π _hπ
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          rw [matchingLocalProjection_apply_mul_tau]
    _ =
        ∑ π : Perm α,
          (F π - matchingLocalProjection M F π) ^ (2 : ℕ) := by
          exact
            sum_perm_cube_right_tau_div_card M
              (fun σ : Perm α =>
                (F σ - matchingLocalProjection M F σ) ^ (2 : ℕ))

end DictatorshipTesting
