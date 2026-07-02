import DictatorshipTesting.Paper.Aux_CubeDeltaFourier
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-!
# Parseval for cube square differences
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- For fixed directions, Parseval expresses the square-difference energy as a
Fourier coefficient sum with the usual multiplier. -/
theorem cubeDelta_parseval {m : ℕ} (g : Cube m → ℝ) (u v : Cube m) :
    cubeExpectation (fun x : Cube m => (cubeDelta g x u v) ^ (2 : ℕ)) =
      ∑ S : Finset (Fin m),
        (cubeFourierCoeff g S * (1 - cubeChar S u) *
          (1 - cubeChar S v)) ^ (2 : ℕ) := by
  calc
    cubeExpectation (fun x : Cube m => (cubeDelta g x u v) ^ (2 : ℕ))
        =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff (fun x : Cube m => cubeDelta g x u v) S) ^ (2 : ℕ) := by
          exact L2_3_cubeParseval_identity m (fun x : Cube m => cubeDelta g x u v)
    _ =
        ∑ S : Finset (Fin m),
          (cubeFourierCoeff g S * (1 - cubeChar S u) *
            (1 - cubeChar S v)) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [cubeFourierCoeff_cubeDelta]

end DictatorshipTesting
