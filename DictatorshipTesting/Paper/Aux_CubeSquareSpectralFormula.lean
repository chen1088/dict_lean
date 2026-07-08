import DictatorshipTesting.Paper.Aux_CubeFourierTranslate
import DictatorshipTesting.Paper.Aux_CubeHighDegreeLinear
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper.Aux_CubeColorCounting`
- `DictatorshipTesting.PaperAux`
-/

/-!
# Spectral formula for the cube square-test energy
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Translating a cube function on the right by xor has the same Fourier effect
as translating on the left. -/
theorem cubeFourierCoeff_xor_right {m : ℕ} (g : Cube m → ℝ)
    (z : Cube m) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun y => g (cubeXor y z)) S =
      cubeChar S z * cubeFourierCoeff g S := by
  simpa [cubeXor_comm] using cubeFourierCoeff_xor_left g z S

/-- The Fourier coefficient of a mixed cube difference is multiplied by the
corresponding character difference factors. -/
theorem cubeFourierCoeff_cubeDelta {m : ℕ} (g : Cube m → ℝ)
    (u v : Cube m) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun x => cubeDelta g x u v) S =
      cubeFourierCoeff g S * (1 - cubeChar S u) * (1 - cubeChar S v) := by
  unfold cubeDelta
  have hlast :
      cubeFourierCoeff
          (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S =
        cubeChar S u * cubeChar S v * cubeFourierCoeff g S := by
    calc
      cubeFourierCoeff
          (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S
          =
          cubeFourierCoeff
            (fun x : Cube m => g (cubeXor x (cubeXor u v))) S := by
            congr 1
            ext x
            rw [cubeXor_assoc]
      _ = cubeChar S (cubeXor u v) * cubeFourierCoeff g S := by
            rw [cubeFourierCoeff_xor_right]
      _ = cubeChar S u * cubeChar S v * cubeFourierCoeff g S := by
            rw [cubeChar_cubeXor]
  calc
    cubeFourierCoeff
        (fun x : Cube m =>
          g x - g (cubeXor x u) - g (cubeXor x v) +
            g (cubeXor (cubeXor x u) v)) S
        =
        cubeFourierCoeff
          (fun x : Cube m =>
            g x + (-1) * g (cubeXor x u) +
              ((-1) * g (cubeXor x v) +
                g (cubeXor (cubeXor x u) v))) S := by
          congr 1
          ext x
          ring
    _ =
        cubeFourierCoeff g S +
          cubeFourierCoeff (fun x : Cube m => (-1) * g (cubeXor x u)) S +
            (cubeFourierCoeff (fun x : Cube m => (-1) * g (cubeXor x v)) S +
              cubeFourierCoeff
                (fun x : Cube m => g (cubeXor (cubeXor x u) v)) S) := by
          rw [cubeFourierCoeff_add]
          rw [cubeFourierCoeff_add]
          rw [cubeFourierCoeff_add]
    _ =
        cubeFourierCoeff g S +
          (-1) * (cubeChar S u * cubeFourierCoeff g S) +
            ((-1) * (cubeChar S v * cubeFourierCoeff g S) +
              cubeChar S u * cubeChar S v * cubeFourierCoeff g S) := by
          rw [cubeFourierCoeff_smul, cubeFourierCoeff_smul]
          rw [cubeFourierCoeff_xor_right, cubeFourierCoeff_xor_right, hlast]
    _ = cubeFourierCoeff g S * (1 - cubeChar S u) * (1 - cubeChar S v) := by
          ring

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
          intro S _hS
          rw [cubeFourierCoeff_cubeDelta]

/-- The square-test energy can be viewed as first averaging over the cube for
each color choice, and then averaging over colors. -/
theorem cubeSquareEnergy_eq_color_average {m : ℕ} (g : Cube m → ℝ) :
    cubeSquareEnergy g =
      (∑ c : CubeDirectionColor m,
        cubeExpectation
          (fun x : Cube m =>
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ))) /
        (Fintype.card (CubeDirectionColor m) : ℝ) := by
  unfold cubeSquareEnergy cubeExpectation
  calc
    (∑ x : Cube m,
        (∑ c : CubeDirectionColor m,
          (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
      (Fintype.card (Cube m) : ℝ)
        =
        ((∑ x : Cube m,
          ∑ c : CubeDirectionColor m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [← Finset.sum_div]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ)) /
          (Fintype.card (Cube m) : ℝ) := by
          rw [Finset.sum_comm]
    _ =
        ((∑ c : CubeDirectionColor m,
          ∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
            (Fintype.card (Cube m) : ℝ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ) := by
          ring_nf
    _ =
        (∑ c : CubeDirectionColor m,
          (∑ x : Cube m,
            (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
              (Fintype.card (Cube m) : ℝ)) /
            (Fintype.card (CubeDirectionColor m) : ℝ) := by
          rw [Finset.sum_div]

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
