import DictatorshipTesting.Paper.Defs.S02_IntDef_OneCosetReal
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_IntDef_L2DistSq`
- `DictatorshipTesting.Paper.S02_Thm2_01_BooleanU1Classification`
-/


/-!
Definition file for `U1`.
-/

noncomputable section

namespace DictatorshipTesting

/-- The global degree-one space `U₁ = span {tᵢⱼ}`. -/
def U1 (α : Type*) [Fintype α] [DecidableEq α] : Submodule ℝ (Perm α → ℝ) :=
  Submodule.span ℝ
    (Set.range fun ij : α × α => oneCosetReal ij.1 ij.2)

end DictatorshipTesting
