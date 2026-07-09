import DictatorshipTesting.Paper.Defs.S02_Def2_20_CubeDelta
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_22_IsCubeConstant`
-/


/-!
Definition file for `CubeDirectionsDisjoint`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Two cube directions are disjoint when no coordinate is used in both. -/
def CubeDirectionsDisjoint {m : ℕ} (u v : Cube m) : Prop :=
  ∀ r, u r = true → v r = false

end DictatorshipTesting
