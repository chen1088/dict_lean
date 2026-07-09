import DictatorshipTesting.Paper.Defs.S03_Def3_04_OrderedMatchingTau
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_06_CubeDirectionColor`
- `DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta`
-/


/-!
Definition file for `matchingCubeRestriction`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Restrict a Boolean function on permutations to a matching cube based at `pi`. -/
def matchingCubeRestriction {α : Type*} [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α) :
    Cube M.edgeCount → Bool :=
  fun x => f (π * M.tau x)

end DictatorshipTesting
