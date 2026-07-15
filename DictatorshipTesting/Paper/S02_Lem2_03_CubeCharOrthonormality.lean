import AlgebraicLibrary.BooleanCube.Fourier
import AlgebraicLibrary.BooleanCube.Basic

open AlgebraicLibrary

/-! Paper-facing compatibility statements for Lemma 2.3 orthonormality. -/

namespace DictatorshipTesting

theorem S02_Lem2_03_cubeChar_orthonormality (m : ℕ) :
    ∀ S T : Finset (Fin m),
      cubeExpectation (fun x : FinCube m => cubeChar S x * cubeChar T x) =
        if S = T then 1 else 0 := by
  intro S T
  exact AlgebraicLibrary.cubeChar_orthonormality S T

end DictatorshipTesting
