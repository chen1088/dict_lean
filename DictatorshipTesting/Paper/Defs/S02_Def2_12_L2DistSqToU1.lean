import DictatorshipTesting.Paper.Defs.S02_Def2_11_L2DistSq
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_13_Cube`
- `DictatorshipTesting.Paper.S02_Thm2_02_FKNStability`
-/


/-!
Definition file for `l2DistSqToU1`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Squared distance from a function to `U₁`, equivalent to `‖f - P_{U₁} f‖²`. -/
def l2DistSqToU1 {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ G : Perm α → ℝ, G ∈ U1 α ∧ d = l2DistSq F G}

end DictatorshipTesting
