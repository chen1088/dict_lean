import DictatorshipTesting.Paper.Aux_CubeDeltaParseval
import DictatorshipTesting.Paper.Aux_CubeSquareEnergyAverage

/-!
# Spectral formula for the cube square-test energy
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The average square-test multiplier for one cube character. -/
def cubeColorMultiplierAverage {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  (∑ c : CubeDirectionColor m,
    ((1 - cubeChar S (cubeColorU c)) *
      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
    (Fintype.card (CubeDirectionColor m) : ℝ)

/-- The cube square-test energy decomposes diagonally in the Fourier basis. -/
theorem cubeSquareEnergy_spectral_formula {m : ℕ} (g : Cube m → ℝ) :
    cubeSquareEnergy g =
      ∑ S : Finset (Fin m),
        (cubeFourierCoeff g S) ^ (2 : ℕ) * cubeColorMultiplierAverage S := by
  rw [cubeSquareEnergy_eq_color_average]
  unfold cubeColorMultiplierAverage
  calc
    (∑ c : CubeDirectionColor m,
        cubeExpectation
          (fun x : Cube m =>
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ))) /
        (Fintype.card (CubeDirectionColor m) : ℝ)
        =
        (∑ c : CubeDirectionColor m,
          ∑ S : Finset (Fin m),
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          rw [cubeDelta_parseval]
    _ =
        (∑ S : Finset (Fin m),
          ∑ c : CubeDirectionColor m,
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          rw [Finset.sum_comm]
    _ =
        ∑ S : Finset (Fin m),
          ((∑ c : CubeDirectionColor m,
            (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
              (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) := by
          rw [Finset.sum_div]
    _ =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff g S) ^ (2 : ℕ) *
            ((∑ c : CubeDirectionColor m,
              ((1 - cubeChar S (cubeColorU c)) *
                (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
              (Fintype.card (CubeDirectionColor m) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro S _
          calc
            (∑ c : CubeDirectionColor m,
              (cubeFourierCoeff g S * (1 - cubeChar S (cubeColorU c)) *
                (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                (Fintype.card (CubeDirectionColor m) : ℝ)
                =
                (∑ c : CubeDirectionColor m,
                  (cubeFourierCoeff g S) ^ (2 : ℕ) *
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                  (Fintype.card (CubeDirectionColor m) : ℝ) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro c _
                  ring
            _ =
                ((cubeFourierCoeff g S) ^ (2 : ℕ) *
                  (∑ c : CubeDirectionColor m,
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ))) /
                  (Fintype.card (CubeDirectionColor m) : ℝ) := by
                  congr 1
                  rw [Finset.mul_sum]
            _ =
                (cubeFourierCoeff g S) ^ (2 : ℕ) *
                  ((∑ c : CubeDirectionColor m,
                    ((1 - cubeChar S (cubeColorU c)) *
                      (1 - cubeChar S (cubeColorV c))) ^ (2 : ℕ)) /
                    (Fintype.card (CubeDirectionColor m) : ℝ)) := by
                  ring

end DictatorshipTesting
