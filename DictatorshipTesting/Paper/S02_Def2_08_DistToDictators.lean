import DictatorshipTesting.Paper.S02_Def2_07_HammingDist

/-!
Definition file for `distToDictators`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Distance to the dictator class. -/
def distToDictators {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) : ℝ :=
  sInf {d : ℝ | ∃ g : BoolFn α, IsDictator g ∧ d = hammingDist f g}

end DictatorshipTesting
