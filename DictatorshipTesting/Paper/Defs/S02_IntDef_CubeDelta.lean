import DictatorshipTesting.Paper.Defs.S02_IntDef_CubeZero
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_CubeDirectionsDisjoint`
-/


/-!
Definition file for `cubeDelta`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The mixed second difference on a Boolean-cube square. -/
def cubeDelta {m : ℕ} (g : Cube m → ℝ) (x u v : Cube m) : ℝ :=
  g x - g (cubeXor x u) - g (cubeXor x v) + g (cubeXor (cubeXor x u) v)

end DictatorshipTesting
