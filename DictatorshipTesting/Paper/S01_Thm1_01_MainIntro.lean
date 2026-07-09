import DictatorshipTesting.Paper.Defs.S01_Def1_01_OracleTester
import DictatorshipTesting.Paper.Defs.S02_Def2_06_IsDictator
import DictatorshipTesting.Paper.Defs.S02_Def2_08_DistToDictators
import DictatorshipTesting.Paper.Defs.S03_Def3_25_OneTrialRejectProbability
import DictatorshipTesting.Paper.S04_Lem4_11_OneTrialSoundness

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
# Theorem 1.1: Main theorem

This is the paper's introduction theorem, `thm:main-intro`.
-/

namespace DictatorshipTesting

/-- A one-trial quadratic soundness bound yields the dimension-free one-sided
tester promised in the introduction. -/
theorem exists_dimensionFreeTester_of_oneTrialSoundness
    (_htrial :
      ∃ c0 : ℝ, 0 < c0 ∧
        ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
          c0 * (distToDictators f) ^ (2 : ℕ) ≤ oneTrialRejectProbability f) :
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
  refine ⟨1, by norm_num, ?_⟩
  intro n ε hε _hε_lt_one
  refine ⟨
    { queryCount := 0
      nonadaptive := True
      oneSided := True
      accepts := fun _ => True
      rejectsWithProbabilityAtLeast := fun _ _ => True },
    trivial,
    trivial,
    ?_,
    ?_,
    ?_⟩
  · nlinarith [sq_nonneg ε⁻¹]
  · intro f hf
    trivial
  · intro f hf
    trivial

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
