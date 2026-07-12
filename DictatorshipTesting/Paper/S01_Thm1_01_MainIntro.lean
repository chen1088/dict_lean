import DictatorshipTesting.Paper.Defs.S02_Def2_01_FiniteSeedTester
import DictatorshipTesting.Paper.S04_Lem4_10_IndependentRepetitionAndAmplification

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
# Theorem 1.1: Main theorem

This is the paper's introduction theorem, `thm:main-intro`.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Theorem 1.1, `thm:main-intro`: a dimension-free one-sided tester exists,
using the one-trial soundness theorem. -/
theorem S01_Thm1_01_MainIntro :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ tester : OracleTester (Fin n),
          tester.nonadaptive ∧
          tester.oneSided ∧
          (tester.queryCount : ℝ) ≤ C * ε⁻¹ ^ (2 : ℕ) ∧
          (∀ f : BoolFn (Fin n), IsDictator f → tester.accepts f) ∧
          (∀ f : BoolFn (Fin n),
            ε ≤ distToDictators f →
              tester.rejectsWithProbabilityAtLeast f ((2 : ℝ) / 3)) := by
  exact S04_Lem4_10_dimension_free_amplification
    S04_Lem4_09_OneTrialSoundness

end DictatorshipTesting
