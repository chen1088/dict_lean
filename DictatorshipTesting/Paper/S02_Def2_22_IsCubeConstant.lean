import DictatorshipTesting.Paper.S02_Def2_21_CubeDirectionsDisjoint

/-!
Definition file for `IsCubeConstant`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function is constant. -/
def IsCubeConstant {m : ℕ} (g : Cube m → Bool) : Prop :=
  ∀ x y, g x = g y

end DictatorshipTesting
