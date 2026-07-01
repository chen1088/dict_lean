import DictatorshipTesting.Paper.Aux_DistanceNonneg
import DictatorshipTesting.Paper.L5_2_SpectralCertificate
import DictatorshipTesting.Paper.L5_5_HEvenApp
import DictatorshipTesting.Paper.L5_6_HOddApp

/-!
# Theorem 4.10: Matching-cube spectral gap

This is `thm:matching-gap` from `soda27authors_section5_rethought.tex`.
-/

namespace DictatorshipTesting

/-- Theorem 4.10, `thm:matching-gap`: matching-cube spectral gap. -/
theorem Thm4_10_MatchingGap (n : ℕ) (hn : 4 ≤ n)
    (F : Perm (Fin n) → ℝ) :
    (1 / 6 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F ∧
      (Even n → (1 / 5 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases (even_iff_exists_two_mul.mp heven) with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hgap15 : MatchingSpectralGapConstant (2 * m) (1 / 5 : ℝ) := by
      exact (L5_2_SpectralCertificate m (1 / 5 : ℝ)).1
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
      exact (L5_2_SpectralCertificate m (1 / 6 : ℝ)).2
        (by norm_num)
        (by
          intro lam hrow hstd
          exact L5_6_HOddApp m hm lam hrow hstd)
    constructor
    · exact hgap16 F
    · intro heven
      exact False.elim (hnotEven heven)

end DictatorshipTesting
