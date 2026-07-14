import DictatorshipTesting.Paper.Defs.S03_IntDef_CubeSquareEnergy
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S04_Def4_01_MatchingLocalDegreeOneAndProjection`
-/


/-!
Definition file for `permInner`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Normalized inner product on real-valued functions on a finite symmetric group. -/
def permInner {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, F π * G π) / (Fintype.card (Perm α) : ℝ)

end DictatorshipTesting
