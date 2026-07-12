import DictatorshipTesting.Paper.Defs.S02_IntDef_HammingDist
/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S02_Def2_01_FiniteSeedTester`
- `DictatorshipTesting.Paper.S04_Lem4_10_IndependentRepetitionAndAmplification`
-/


/-!
Definition file for `distToDictators`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Distance to the dictator class. -/
def distToDictators {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) : ℝ :=
  sInf {d : ℝ | ∃ g : BoolFn α, IsDictator g ∧ d = hammingDist f g}

end DictatorshipTesting
