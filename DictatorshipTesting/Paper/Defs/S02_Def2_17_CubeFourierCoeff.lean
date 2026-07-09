import DictatorshipTesting.Paper.Defs.S02_Def2_16_CubeExpectation

/-!
Definition file for `cubeFourierCoeff`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Fourier coefficient of a real-valued function on the Boolean cube. -/
def cubeFourierCoeff {m : ℕ} (g : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  cubeExpectation fun x => g x * cubeChar S x

end DictatorshipTesting
