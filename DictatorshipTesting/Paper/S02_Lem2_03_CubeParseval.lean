import DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality
import DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParsevalIdentity

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S02_Def2_02a_CubeLowDegreeOnePart`
- `DictatorshipTesting.Paper.Defs.S04_Def4_01_MatchingLocalDegreeOneAndProjection`
- `DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare`
- `DictatorshipTesting.Paper.S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne`
- `DictatorshipTesting.Paper.S04_Prop4_02_CosetwiseDescriptionOfPM`
-/
/-!
# Lemma 2.3: Orthonormality and Parseval on the cube

This is the paper's cube Fourier lemma, `lem:cube-parseval`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Lemma 2.3, `lem:cube-parseval`: cube characters are orthonormal and give
Fourier expansion plus Parseval. -/
theorem S02_Lem2_03_CubeParseval (m : ℕ) :
    (∀ S T : Finset (Fin m),
      cubeExpectation (fun x : Cube m => cubeChar S x * cubeChar T x) =
        if S = T then 1 else 0) ∧
    (∀ g : Cube m → ℝ, ∀ x : Cube m,
      g x = ∑ S : Finset (Fin m), cubeFourierCoeff g S * cubeChar S x) ∧
    (∀ g : Cube m → ℝ,
      cubeExpectation (fun x : Cube m => g x ^ (2 : ℕ)) =
        ∑ S : Finset (Fin m), (cubeFourierCoeff g S) ^ (2 : ℕ)) := by
  exact ⟨S02_Lem2_03_cubeChar_orthonormality m, S02_Lem2_03_cubeFourier_expansion m,
    S02_Lem2_03_cubeParseval_identity m⟩

end DictatorshipTesting
