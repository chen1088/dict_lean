import DictatorshipTesting.Paper.Aux_CubeLowDegreeError

/-!
# Cube Fourier inner products

This file records the elementary inner-product form of Parseval and the
orthogonality of the high-degree residual to degree-at-most-one functions.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Cube inner product in the Fourier basis. -/
theorem cubeExpectation_mul_eq_sum_fourierCoeff {m : ℕ}
    (g h : Cube m → ℝ) :
    cubeExpectation (fun x : Cube m => g x * h x) =
      ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeFourierCoeff h S := by
  classical
  let N : ℝ := Fintype.card (Cube m)
  calc
    cubeExpectation (fun x : Cube m => g x * h x)
        =
        cubeExpectation
          (fun x : Cube m =>
            g x * (∑ S : Finset (Fin m),
              cubeFourierCoeff h S * cubeChar S x)) := by
          congr
          ext x
          rw [← L2_3_cubeFourier_expansion m h x]
    _ = ∑ S : Finset (Fin m), cubeFourierCoeff h S *
          cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
          calc
            cubeExpectation
                (fun x : Cube m =>
                  g x * (∑ S : Finset (Fin m),
                    cubeFourierCoeff h S * cubeChar S x))
                =
                (∑ x : Cube m,
                  g x * (∑ S : Finset (Fin m),
                    cubeFourierCoeff h S * cubeChar S x)) / N := by
                    simp [cubeExpectation, N]
            _ = (∑ x : Cube m,
                  ∑ S : Finset (Fin m),
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x _
                    rw [Finset.mul_sum]
            _ = (∑ S : Finset (Fin m),
                  ∑ x : Cube m,
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    rw [Finset.sum_comm]
            _ = ∑ S : Finset (Fin m),
                  (∑ x : Cube m,
                    g x * (cubeFourierCoeff h S * cubeChar S x)) / N := by
                    rw [Finset.sum_div]
            _ = ∑ S : Finset (Fin m), cubeFourierCoeff h S *
                  cubeExpectation (fun x : Cube m => g x * cubeChar S x) := by
                    apply Finset.sum_congr rfl
                    intro S _
                    unfold cubeExpectation
                    calc
                      (∑ x : Cube m,
                          g x * (cubeFourierCoeff h S * cubeChar S x)) / N
                          =
                          (cubeFourierCoeff h S *
                            (∑ x : Cube m, g x * cubeChar S x)) / N := by
                            congr 1
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro x _
                            ring
                      _ = cubeFourierCoeff h S *
                            ((∑ x : Cube m, g x * cubeChar S x) / N) := by
                            ring
                      _ = cubeFourierCoeff h S *
                            ((∑ x : Cube m, g x * cubeChar S x) /
                              (Fintype.card (Cube m) : ℝ)) := by
                            simp [N]
    _ = ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeFourierCoeff h S := by
          apply Finset.sum_congr rfl
          intro S _
          unfold cubeFourierCoeff
          ring

/-- The high-degree residual is orthogonal to every degree-at-most-one cube
function. -/
theorem cubeExpectation_lowDegreeResidual_mul_of_highDegreeEnergy_eq_zero
    {m : ℕ} (g h : Cube m → ℝ) (hh : cubeHighDegreeEnergy h = 0) :
    cubeExpectation
        (fun x : Cube m => (g x - cubeLowDegreeOnePart g x) * h x) = 0 := by
  rw [cubeExpectation_mul_eq_sum_fourierCoeff]
  apply Finset.sum_eq_zero
  intro S _hS
  by_cases hhigh : 2 ≤ S.card
  · have hcoeff :
        cubeFourierCoeff h S = 0 :=
      cubeFourierCoeff_eq_zero_of_cubeHighDegreeEnergy_eq_zero hh hhigh
    simp [cubeFourierCoeff_lowDegreeResidual, hhigh, hcoeff]
  · simp [cubeFourierCoeff_lowDegreeResidual, hhigh]

end DictatorshipTesting
