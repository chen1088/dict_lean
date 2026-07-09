import DictatorshipTesting.Paper.Defs.S03_Def3_13_CubeSquareEnergy
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S03_Def3_15_IsMatchingLocalDegreeOne`
-/


/-!
Definition file for `permInner`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Normalized inner product on real-valued functions on a finite symmetric group. -/
def permInner {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, F π * G π) / (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
