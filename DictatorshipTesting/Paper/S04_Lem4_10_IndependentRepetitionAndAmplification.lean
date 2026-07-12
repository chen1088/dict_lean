/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S01_Thm1_01_MainIntro

/-!
Paper statement: Lemma 4.10 (`lem:independent-repetition`).
-/

namespace DictatorshipTesting

theorem S04_Lem4_10_repetition_rejection_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (tester : OracleTester α) (f : BoolFn α) :
    (repeatTester k tester).rejectionProbability f =
      1 - (1 - tester.rejectionProbability f) ^ k :=
  repeatTester_rejectionProbability k tester f

theorem S04_Lem4_10_dimension_free_amplification
    (htrial :
      ∃ c0 : ℝ, 0 < c0 ∧
        ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
          c0 * distToDictators f ^ (2 : ℕ) ≤ oneTrialRejectProbability f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ tester : OracleTester (Fin n),
          tester.nonadaptive ∧ tester.oneSided ∧
          (tester.queryCount : ℝ) ≤ C * ε⁻¹ ^ (2 : ℕ) ∧
          (∀ f : BoolFn (Fin n), IsDictator f → tester.accepts f) ∧
          (∀ f : BoolFn (Fin n), ε ≤ distToDictators f →
            tester.rejectsWithProbabilityAtLeast f ((2 : ℝ) / 3)) :=
  exists_dimensionFreeTester_of_oneTrialSoundness htrial

end DictatorshipTesting
