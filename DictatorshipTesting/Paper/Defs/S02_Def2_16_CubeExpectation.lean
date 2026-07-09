import DictatorshipTesting.Paper.Defs.S02_Def2_15_CubeFlip
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_17_CubeFourierCoeff`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeCharOrthonormality`
-/


/-!
Definition file for `cubeExpectation`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Uniform expectation on the Boolean cube. -/
def cubeExpectation {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  (∑ x : Cube m, g x) / (Fintype.card (Cube m) : ℝ)

end DictatorshipTesting
