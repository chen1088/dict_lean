import DictatorshipTesting.Paper.Aux_OneTrialRejectProbabilityLowerBound
import DictatorshipTesting.Paper.S04_Prop4_12_SquareEnergyControlsGlobalDegree
import DictatorshipTesting.Paper.S02_Thm2_02_FKNStability

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S01_Thm1_01_MainIntro`
-/

/-!
# Lemma 4.13: One-trial soundness

This is `lem:one-trial-soundness` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Lemma 4.13, `lem:one-trial-soundness`: one-trial soundness. -/
theorem L4_13_OneTrialSoundness :
    ∃ c0 : ℝ, 0 < c0 ∧
      ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
        c0 * (distToDictators f) ^ (2 : ℕ) ≤ oneTrialRejectProbability f := by
  rcases Thm2_2_FKNInput with ⟨cFKN, hcFKN_pos, hFKN⟩
  refine ⟨(4 / 27 : ℝ) * cFKN, ?_, ?_⟩
  · nlinarith
  · intro n hn f
    have hFKN_nf :
        cFKN * (distToDictators f) ^ (2 : ℕ) ≤
          l2DistSqToU1 (boolFnToReal f) :=
      hFKN n hn f
    have hsquare :
        (16 / 27 : ℝ) * l2DistSqToU1 (boolFnToReal f) ≤
          oneTrialDeltaSqExpectation (boolFnToReal f) :=
      Prop4_12_SquareEnergyControlsGlobalDegree n hn (boolFnToReal f)
    have hreject :
        (1 / 4 : ℝ) * oneTrialDeltaSqExpectation (boolFnToReal f) ≤
          oneTrialRejectProbability f :=
      oneTrialRejectProbability_ge_deltaSqExpectation n f
    calc
      ((4 / 27 : ℝ) * cFKN) * (distToDictators f) ^ (2 : ℕ)
          ≤ (4 / 27 : ℝ) * l2DistSqToU1 (boolFnToReal f) := by
            nlinarith
      _ ≤ (1 / 4 : ℝ) * oneTrialDeltaSqExpectation (boolFnToReal f) := by
            nlinarith
      _ ≤ oneTrialRejectProbability f := hreject

end DictatorshipTesting
