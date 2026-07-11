import DictatorshipTesting.Paper.Defs.S02_IntDef_IsDictator
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_DistToDictators`
-/


/-!
Definition file for `hammingDist`.
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
