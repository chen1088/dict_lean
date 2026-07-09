import DictatorshipTesting.Paper.S02_Def2_15_CubeFlip

/-!
Definition file for `cubeExpectation`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Uniform expectation on the Boolean cube. -/
def cubeExpectation {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  (∑ x : Cube m, g x) / (Fintype.card (Cube m) : ℝ)

end DictatorshipTesting
