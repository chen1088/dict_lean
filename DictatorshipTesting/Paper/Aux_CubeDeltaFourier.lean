import DictatorshipTesting.Paper.Aux_CubeFourierTranslate
import DictatorshipTesting.Paper.Aux_CubeHighDegreeLinear

/-!
# Fourier coefficients of cube square differences
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

end DictatorshipTesting
