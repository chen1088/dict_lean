import DictatorshipTesting.Paper.Defs.S03_IntDef_PermInner
/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S04_Def4_01b_MatchingLocalHighDegreeEnergy`
- `DictatorshipTesting.Paper.S04_Lem4_06_TijLocalDegree`
-/


/-!
Definition file for `IsMatchingLocalDegreeOne`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- A function is locally degree one on every matching cube for `M`. -/
def IsMatchingLocalDegreeOne {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : Prop :=
  ∀ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x)) = 0

end DictatorshipTesting
