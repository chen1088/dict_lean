import DictatorshipTesting.Paper.Aux_OrderedMatchingTauMul
import DictatorshipTesting.Paper.Aux_PermCubeAverage
import DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare
import DictatorshipTesting.Paper.S04_Lem4_06_LocalHighDegreeErrorFormula

/-!
# Global one-trial square-energy bridge

This packages the probabilistic sampling step from Lemma 4.11 together with the
local cube-square bound and the local projection error formula.
-/

noncomputable section

namespace DictatorshipTesting

/-- A cube delta at basepoint `x` is the trial delta based at `π * tau x`. -/
theorem cubeDelta_restriction_eq_matchingTrialDeltaReal_mul_tau {α : Type*}
    [Fintype α] [DecidableEq α] (F : Perm α → ℝ) (M : OrderedMatching α)
    (π : Perm α) (x : Cube M.edgeCount) (c : CubeDirectionColor M.edgeCount) :
    cubeDelta (fun y : Cube M.edgeCount => F (π * M.tau y))
        x (cubeColorU c) (cubeColorV c) =
      matchingTrialDeltaReal F M (π * M.tau x) c := by
  simp [matchingTrialDeltaReal, cubeDelta, orderedMatching_tau_mul,
    cubeXor_zero, cubeZero_xor, cubeXor_assoc, mul_assoc]

/-- Averaging cube square energy over all base permutations is the same as
averaging the trial delta at the cube origin over all base permutations. -/
theorem sum_perm_cubeSquareEnergy_eq_sum_perm_trialDelta
    {n : ℕ} (F : Perm (Fin n) → ℝ) (M : NearPerfectMatching n) :
    (∑ π : Perm (Fin n),
        cubeSquareEnergy
          (fun x : Cube (n / 2) => F (π * M.toOrdered.tau x))) =
      ∑ π : Perm (Fin n),
        (∑ c : CubeDirectionColor (n / 2),
          (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ) := by
  let e : Perm (Fin n) → ℝ := fun σ =>
    (∑ c : CubeDirectionColor (n / 2),
      (matchingTrialDeltaReal F M.toOrdered σ c) ^ (2 : ℕ)) /
      (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)
  have htranslate :
      (∑ π : Perm (Fin n),
          (∑ x : Cube (n / 2), e (π * M.toOrdered.tau x)) /
            (Fintype.card (Cube (n / 2)) : ℝ)) =
        ∑ π : Perm (Fin n), e π :=
    sum_perm_cube_right_tau_div_card M.toOrdered e
  calc
    (∑ π : Perm (Fin n),
        cubeSquareEnergy
          (fun x : Cube (n / 2) => F (π * M.toOrdered.tau x)))
        =
        ∑ π : Perm (Fin n),
          (∑ x : Cube (n / 2), e (π * M.toOrdered.tau x)) /
            (Fintype.card (Cube (n / 2)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro π _hπ
          unfold cubeSquareEnergy e
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          congr 1
          apply Finset.sum_congr rfl
          intro c _hc
          change
            (cubeDelta
                (fun y : Cube M.toOrdered.edgeCount => F (π * M.toOrdered.tau y))
                x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ) =
              (matchingTrialDeltaReal F M.toOrdered
                (π * M.toOrdered.tau x) c) ^ (2 : ℕ)
          rw [cubeDelta_restriction_eq_matchingTrialDeltaReal_mul_tau]
    _ = ∑ π : Perm (Fin n), e π := htranslate
    _ =
        ∑ π : Perm (Fin n),
          (∑ c : CubeDirectionColor (n / 2),
            (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor (n / 2)) : ℝ) := rfl

/-- The mean square of one matching-cube trial controls the mean matching-local
projection error. -/
theorem oneTrialDeltaSqExpectation_ge_matchingMeanProjectionError
    (n : ℕ) (F : Perm (Fin n) → ℝ) :
    (32 / 9 : ℝ) * matchingMeanProjectionError F ≤
      oneTrialDeltaSqExpectation F := by
  classical
  unfold matchingMeanProjectionError oneTrialDeltaSqExpectation
  have hPpos : 0 < (Fintype.card (Perm (Fin n)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Perm (Fin n)))
  have hMpos : 0 < (Fintype.card (NearPerfectMatching n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (NearPerfectMatching n))
  calc
    (32 / 9 : ℝ) *
        ((∑ M : NearPerfectMatching n,
          matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ))
        =
        (∑ M : NearPerfectMatching n,
          (32 / 9 : ℝ) * matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤
        (∑ M : NearPerfectMatching n,
          (∑ π : Perm (Fin n),
            (∑ c : CubeDirectionColor (n / 2),
              (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
              (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
            (Fintype.card (Perm (Fin n)) : ℝ)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
          apply div_le_div_of_nonneg_right ?_ (le_of_lt hMpos)
          apply Finset.sum_le_sum
          intro M _hM
          calc
            (32 / 9 : ℝ) * matchingLocalProjectionError F M.toOrdered
                =
                (32 / 9 : ℝ) * matchingLocalHighDegreeEnergy F M.toOrdered := by
                  rw [L4_6_LocalHighDegreeErrorFormula]
            _ =
                (∑ π : Perm (Fin n),
                  (32 / 9 : ℝ) *
                    cubeHighDegreeEnergy
                      (fun x : Cube (n / 2) => F (π * M.toOrdered.tau x))) /
                  (Fintype.card (Perm (Fin n)) : ℝ) := by
                  unfold matchingLocalHighDegreeEnergy
                  rw [← Finset.mul_sum]
                  rw [mul_div_assoc]
                  rfl
            _ ≤
                (∑ π : Perm (Fin n),
                  cubeSquareEnergy
                    (fun x : Cube (n / 2) => F (π * M.toOrdered.tau x))) /
                  (Fintype.card (Perm (Fin n)) : ℝ) := by
                  apply div_le_div_of_nonneg_right ?_ (le_of_lt hPpos)
                  apply Finset.sum_le_sum
                  intro π _hπ
                  exact L4_1_CubeSquare (n / 2)
                    (fun x : Cube (n / 2) => F (π * M.toOrdered.tau x))
            _ =
                (∑ π : Perm (Fin n),
                  (∑ c : CubeDirectionColor (n / 2),
                    (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
                    (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
                  (Fintype.card (Perm (Fin n)) : ℝ) := by
                  rw [sum_perm_cubeSquareEnergy_eq_sum_perm_trialDelta]

end DictatorshipTesting
