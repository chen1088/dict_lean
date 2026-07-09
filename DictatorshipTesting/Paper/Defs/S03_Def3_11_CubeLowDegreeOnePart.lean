import DictatorshipTesting.Paper.Defs.S03_Def3_10_MatchingTrialDeltaReal
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_12_CubeHighDegreeEnergy`
- `DictatorshipTesting.Paper.S04_Lem4_04_PMIndependentOfRepresentatives`
-/


/-!
Definition file for `cubeLowDegreeOnePart`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
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
