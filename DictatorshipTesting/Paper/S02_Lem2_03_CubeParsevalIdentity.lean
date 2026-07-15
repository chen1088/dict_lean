import DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion
import DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality
import AlgebraicLibrary.BooleanCube.Fourier

open AlgebraicLibrary

/-! Paper-facing compatibility statement for Lemma 2.3 Parseval. -/

namespace DictatorshipTesting

theorem S02_Lem2_03_cubeParseval_identity (m : ℕ) :
    ∀ g : FinCube m → ℝ,
      cubeExpectation (fun x : FinCube m => g x ^ (2 : ℕ)) =
        ∑ S : Finset (Fin m), (cubeFourierCoeff g S) ^ (2 : ℕ) := by
  intro g
  exact AlgebraicLibrary.cubeParseval g

end DictatorshipTesting
