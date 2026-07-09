import DictatorshipTesting.Paper.S03_Def3_04_OrderedMatchingTau

/-!
Definition file for `matchingCubeRestriction`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
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
