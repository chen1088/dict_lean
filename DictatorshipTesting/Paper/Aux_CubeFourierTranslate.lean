import DictatorshipTesting.Paper.Aux_CubeCharMulSelf
import DictatorshipTesting.Paper.Aux_CubeCharXor

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Aux_CubeSquareSpectralFormula`
- `DictatorshipTesting.Paper.S04_Lem4_04_PMIndependentOfRepresentatives`
-/


/-!
# Fourier coefficients under cube translations
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Translating a cube function by xor multiplies Fourier coefficients by the
corresponding character value. -/
theorem cubeFourierCoeff_xor_left {m : ℕ} (g : Cube m → ℝ)
    (z : Cube m) (S : Finset (Fin m)) :
    cubeFourierCoeff (fun y => g (cubeXor z y)) S =
      cubeChar S z * cubeFourierCoeff g S := by
  unfold cubeFourierCoeff cubeExpectation
  have hchange :
      (∑ y : Cube m, g (cubeXor z y) * cubeChar S y) =
        ∑ t : Cube m, g t * cubeChar S (cubeXor z t) := by
    refine Fintype.sum_equiv (cubeXorEquiv z)
      (fun y : Cube m => g (cubeXor z y) * cubeChar S y)
      (fun t : Cube m => g t * cubeChar S (cubeXor z t)) ?_
    intro y
    simp [cubeXorEquiv, cubeXor_self_left]
  have hfactor :
      (∑ t : Cube m, g t * cubeChar S (cubeXor z t)) =
        cubeChar S z * (∑ t : Cube m, g t * cubeChar S t) := by
    calc
      (∑ t : Cube m, g t * cubeChar S (cubeXor z t))
          = ∑ t : Cube m, g t * (cubeChar S z * cubeChar S t) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [cubeChar_cubeXor]
      _ = cubeChar S z * (∑ t : Cube m, g t * cubeChar S t) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              ring
  rw [hchange, hfactor]
  ring

end DictatorshipTesting
