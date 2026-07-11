import DictatorshipTesting.Paper.Defs.S02_IntDef_IsCubeJuntaAt
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_IntDef_OrderedMatching`
-/


/-!
Definition file for `IsCubeOneJunta`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A Boolean cube function depends on at most one coordinate. -/
def IsCubeOneJunta {m : ℕ} (g : Cube m → Bool) : Prop :=
  IsCubeConstant g ∨ ∃ r, IsCubeJuntaAt g r

end DictatorshipTesting
