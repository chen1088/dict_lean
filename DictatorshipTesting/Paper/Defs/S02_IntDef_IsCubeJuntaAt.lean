import DictatorshipTesting.Paper.Defs.S02_IntDef_IsCubeConstant
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_IsCubeOneJunta`
-/


/-!
Definition file for `IsCubeJuntaAt`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function depends only on coordinate `r`. -/
def IsCubeJuntaAt {m : ℕ} (g : Cube m → Bool) (r : Fin m) : Prop :=
  ∀ x y, x r = y r → g x = g y

end DictatorshipTesting
