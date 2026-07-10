import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingSpectralGapConstant
import DictatorshipTesting.Paper.S05_Lem5_20_EvenSpectralBridge
import DictatorshipTesting.Paper.S05_Lem5_21_OddSpectralBridge

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Prop4_10_SquareEnergyControlsGlobalDegree`
-/


/-!
# Theorem 4.8: Matching-cube spectral gap

This is `thm:matching-gap` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Squared `L^2` distance is nonnegative. -/
theorem l2DistSq_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) :
    0 ≤ l2DistSq F G := by
  unfold l2DistSq
  positivity

/-- Squared distance to `U_1` is nonnegative. -/
theorem l2DistSqToU1_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) :
    0 ≤ l2DistSqToU1 F := by
  unfold l2DistSqToU1
  apply Real.sInf_nonneg
  intro d hd
  rcases hd with ⟨G, _hG, rfl⟩
  exact l2DistSq_nonneg F G

/-- Theorem 4.8, `thm:matching-gap`: matching-cube spectral gap.  The active
theorem path uses the tableau-count Section 5 bridge, with Appendix A supplying
the dimension-parameterized spectral-block model input. -/
theorem Thm4_10_MatchingGap
    (n : ℕ) (hn : 4 ≤ n)
    (F : Perm (Fin n) → ℝ) :
    (1 / 6 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F ∧
      (Even n → (1 / 5 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases (even_iff_exists_two_mul.mp heven) with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hgap15 : MatchingSpectralGapConstant (2 * m) (1 / 5 : ℝ) := by
      exact S05_Lem5_20_tableauDim_evenSpectralGapFromCertificates
        m hm (spectralBlockModelInputWithDim_even_from_appendixA m hm)
    constructor
    · have hscale :
          (1 / 6 : ℝ) * l2DistSqToU1 F ≤
            (1 / 5 : ℝ) * l2DistSqToU1 F := by
        nlinarith [l2DistSqToU1_nonneg F]
      exact le_trans hscale (hgap15 F)
    · intro _heven
      exact hgap15 F
  · have hnotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    rcases (odd_iff_exists_bit1.mp hodd) with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hgap16 : MatchingSpectralGapConstant (2 * m + 1) (1 / 6 : ℝ) := by
      exact S05_Lem5_21_tableauDim_oddSpectralGapFromCertificates
        m hm (spectralBlockModelInputWithDim_odd_from_appendixA m hm)
    constructor
    · exact hgap16 F
    · intro heven
      exact False.elim (hnotEven heven)

end DictatorshipTesting
