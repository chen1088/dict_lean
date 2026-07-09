import DictatorshipTesting.Paper.Defs.S02_Def2_09_OneCosetReal

/-!
Definition file for `U1`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- The global degree-one space `U₁ = span {tᵢⱼ}`. -/
def U1 (α : Type*) [Fintype α] [DecidableEq α] : Submodule ℝ (Perm α → ℝ) :=
  Submodule.span ℝ
    (Set.range fun ij : α × α => oneCosetReal ij.1 ij.2)

end DictatorshipTesting
