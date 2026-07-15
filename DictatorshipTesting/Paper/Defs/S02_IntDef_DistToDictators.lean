import DictatorshipTesting.Paper.Defs.S02_IntDef_HammingDist
import Mathlib.Algebra.Order.Archimedean.Real.Basic
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_01_FiniteSeedTester`
- `DictatorshipTesting.Paper.S04_Lem4_07_IndependentRepetition`
-/
/-!
Definition file for `distToDictators`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Distance to the dictator class. -/
def distToDictators {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) : ℝ :=
  sInf {d : ℝ | ∃ g : BoolFn α, IsDictator g ∧ d = hammingDist f g}

end DictatorshipTesting
