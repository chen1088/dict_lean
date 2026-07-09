import DictatorshipTesting.Paper.S02_Def2_20_CubeDelta

/-!
Definition file for `CubeDirectionsDisjoint`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Two cube directions are disjoint when no coordinate is used in both. -/
def CubeDirectionsDisjoint {m : ℕ} (u v : Cube m) : Prop :=
  ∀ r, u r = true → v r = false

end DictatorshipTesting
