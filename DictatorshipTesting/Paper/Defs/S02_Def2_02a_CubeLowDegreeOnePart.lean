import DictatorshipTesting.Paper.Defs.S03_IntDef_MatchingTrialDeltaReal
import DictatorshipTesting.Paper.S02_Lem2_03_CubeParseval
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S02_Def2_02b_CubeHighDegreeEnergy`
- `DictatorshipTesting.Paper.S04_Lem4_01_CubeSquare`
- `DictatorshipTesting.Paper.S04_Prop4_02_CosetwiseDescriptionOfPM`
-/
/-!
Definition file for `cubeLowDegreeOnePart`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The degree-at-most-one Fourier truncation on the Boolean cube. -/
def cubeLowDegreeOnePart {m : ℕ} (g : Cube m → ℝ) : Cube m → ℝ :=
  fun x =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ 1)),
      cubeFourierCoeff g S * cubeChar S x

end DictatorshipTesting
