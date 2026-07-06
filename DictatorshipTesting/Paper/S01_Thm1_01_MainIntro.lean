import DictatorshipTesting.Paper.Aux_TesterAmplification
import DictatorshipTesting.Paper.S04_Lem4_13_OneTrialSoundness

/-!
# Theorem 1.1: Main theorem

This is the paper's introduction theorem, `thm:main-intro`.
-/

namespace DictatorshipTesting

/-- Theorem 1.1, `thm:main-intro`: a dimension-free one-sided tester exists,
using the one-trial soundness theorem. -/
theorem Thm1_1_MainIntro :
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
  exact exists_dimensionFreeTester_of_oneTrialSoundness
    L4_13_OneTrialSoundness

end DictatorshipTesting
