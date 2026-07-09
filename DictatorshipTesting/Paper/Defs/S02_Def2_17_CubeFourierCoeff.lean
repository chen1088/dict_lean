import DictatorshipTesting.Paper.Defs.S02_Def2_16_CubeExpectation
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_18_CubeXor`
- `DictatorshipTesting.Paper.S02_Lem2_03_CubeFourierExpansion`
-/


/-!
Definition file for `cubeFourierCoeff`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Fourier coefficient of a real-valued function on the Boolean cube. -/
def cubeFourierCoeff {m : ℕ} (g : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  cubeExpectation fun x => g x * cubeChar S x

end DictatorshipTesting
