import DictatorshipTesting.Paper.Defs.S02_Def2_23_IsCubeJuntaAt
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_01_OrderedMatching`
-/


/-!
Definition file for `IsCubeOneJunta`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function depends on at most one coordinate. -/
def IsCubeOneJunta {m : ℕ} (g : Cube m → Bool) : Prop :=
  IsCubeConstant g ∨ ∃ r, IsCubeJuntaAt g r

end DictatorshipTesting
