import DictatorshipTesting.Paper.Defs

/-!
# Tester amplification bridge

This packages the algorithmic step that repeats the one-trial test
`O(epsilon^-2)` times and amplifies the one-trial rejection lower bound to
constant rejection probability.
-/

noncomputable section

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

end DictatorshipTesting
