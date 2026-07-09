import DictatorshipTesting.Paper.Defs.S02_Def2_22_IsCubeConstant
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_24_IsCubeOneJunta`
-/


/-!
Definition file for `IsCubeJuntaAt`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function depends only on coordinate `r`. -/
def IsCubeJuntaAt {m : ℕ} (g : Cube m → Bool) (r : Fin m) : Prop :=
  ∀ x y, x r = y r → g x = g y

end DictatorshipTesting
