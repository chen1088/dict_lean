import DictatorshipTesting.Paper.S02_Def2_11_L2DistSq

/-!
Definition file for `l2DistSqToU1`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared distance from a function to `U₁`, equivalent to `‖f - P_{U₁} f‖²`. -/
def l2DistSqToU1 {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ G : Perm α → ℝ, G ∈ U1 α ∧ d = l2DistSq F G}

end DictatorshipTesting
