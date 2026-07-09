import DictatorshipTesting.Paper.Defs.S03_Def3_11_CubeLowDegreeOnePart
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_13_CubeSquareEnergy`
- `DictatorshipTesting.Paper.S04_Int_CubeHighDegreeLinear`
-/


/-!
Definition file for `cubeHighDegreeEnergy`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Fourier energy on coefficients of degree at least two. -/
def cubeHighDegreeEnergy {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => 2 ≤ S.card)),
    (cubeFourierCoeff g S) ^ (2 : ℕ)

end DictatorshipTesting
