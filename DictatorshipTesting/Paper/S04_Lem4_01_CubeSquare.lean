import DictatorshipTesting.Paper.Aux_CubeColorCounting

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Aux_OneTrialDeltaSqExpectationLowerBound`
-/

/-!
# Lemma 4.1: Square test detects Fourier weight at least two

This is `lem:cube-square` from `dictatorship_testing_soda27_latest.tex`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 4.1, `lem:cube-square`: square tests detect high Fourier weight. -/
theorem L4_1_CubeSquare (m : ℕ) (g : Cube m → ℝ) :
    (32 / 9 : ℝ) * cubeHighDegreeEnergy g ≤ cubeSquareEnergy g := by
  rw [cubeSquareEnergy_spectral_formula]
  unfold cubeHighDegreeEnergy
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _hS
  by_cases hdeg : 2 ≤ S.card
  · have hcoeff_nonneg : 0 ≤ (cubeFourierCoeff g S) ^ (2 : ℕ) :=
      sq_nonneg _
    have hmul :=
      mul_le_mul_of_nonneg_left
        (cubeColorMultiplierAverage_lower_of_two_le_card (m := m) (S := S) hdeg)
        hcoeff_nonneg
    simpa [hdeg, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hnonneg :
        0 ≤ (cubeFourierCoeff g S) ^ (2 : ℕ) * cubeColorMultiplierAverage S :=
      mul_nonneg (sq_nonneg _) (cubeColorMultiplierAverage_nonneg S)
    simpa [hdeg] using hnonneg

end DictatorshipTesting
