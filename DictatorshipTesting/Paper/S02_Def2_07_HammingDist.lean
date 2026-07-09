import DictatorshipTesting.Paper.S02_Def2_06_IsDictator

/-!
Definition file for `hammingDist`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Normalized Hamming distance on Boolean functions over a finite symmetric group. -/
def hammingDist {α : Type*} [Fintype α] [DecidableEq α]
    (f g : BoolFn α) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun π : Perm α => f π ≠ g π).card : ℝ) /
      (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
