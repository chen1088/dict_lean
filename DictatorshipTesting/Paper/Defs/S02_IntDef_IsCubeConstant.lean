import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeDirectionsDisjoint
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_IsCubeJuntaAt`
-/


/-!
Definition file for `IsCubeConstant`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function is constant. -/
def IsCubeConstant {m : ℕ} (g : Cube m → Bool) : Prop :=
  ∀ x y, g x = g y

end DictatorshipTesting
