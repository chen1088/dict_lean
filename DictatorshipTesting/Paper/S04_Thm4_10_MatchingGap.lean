import DictatorshipTesting.Paper.Aux_DistanceNonneg
import DictatorshipTesting.Paper.S05_Lem5_27_EvenSpectralBridge
import DictatorshipTesting.Paper.S05_Lem5_28_OddSpectralBridge
import DictatorshipTesting.Paper.S05_Lem5_32_EvenCertificate
import DictatorshipTesting.Paper.S05_Lem5_34_OddCertificate

/-!
# Theorem 4.10: Matching-cube spectral gap

This is `thm:matching-gap` from `dictatorship_testing_soda27_latest.tex`.
-/

namespace DictatorshipTesting

/-- Theorem 4.10, `thm:matching-gap`: matching-cube spectral gap.  The active
theorem path still uses the older `youngDim` finite-certificate route, so it
carries the corresponding dimension-branching assumptions explicitly. -/
theorem Thm4_10_MatchingGap
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (n : ℕ) (hn : 4 ≤ n)
    (F : Perm (Fin n) → ℝ) :
    (1 / 6 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F ∧
      (Even n → (1 / 5 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases (even_iff_exists_two_mul.mp heven) with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hgap15 : MatchingSpectralGapConstant (2 * m) (1 / 5 : ℝ) := by
      exact matchingSpectralGap_of_even_young_certificate
        m hm (1 / 5 : ℝ)
        (evenSpectralBlockModelFamily_from_specht_pieri_schur m hm)
        (by norm_num)
        (by
          intro lam hrow hstd
          exact L5_5_HEvenApp m hm lam hrow hstd)
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
      exact matchingSpectralGap_of_odd_young_certificate
        m hm (1 / 6 : ℝ)
        (oddSpectralBlockModelFamily_from_specht_pieri_schur m hm)
        (by norm_num)
        (by
          intro lam hrow hstd
          exact L5_6_HOddApp m hm lam hrow hstd)
    constructor
    · exact hgap16 F
    · intro heven
      exact False.elim (hnotEven heven)

end DictatorshipTesting
