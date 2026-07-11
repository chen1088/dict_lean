import DictatorshipTesting.Paper.Defs.S02_IntDef_U1
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_L2DistSqToU1`
-/


/-!
Definition file for `l2DistSq`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared `L²(Sₙ)` distance between real-valued functions. -/
def l2DistSq {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, (F π - G π) ^ 2) / (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
