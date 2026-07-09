import DictatorshipTesting.Paper.Defs.S02_Def2_10_U1

/-!
Definition file for `l2DistSq`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared `L²(Sₙ)` distance between real-valued functions. -/
def l2DistSq {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, (F π - G π) ^ 2) / (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
