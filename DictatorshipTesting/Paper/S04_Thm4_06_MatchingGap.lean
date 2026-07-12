import DictatorshipTesting.Paper.Defs.S05_IntDef_MatchingSpectralGapConstant
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.S05_Lem5_25_EvenCertificate
import DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Prop4_08_SquareEnergyControlsGlobalDegree`
-/


/-!
# Theorem 4.6: Matching-cube spectral gap

This is `thm:matching-gap` from `dictatorship_testing_stoc27_latest.tex`.
-/

namespace DictatorshipTesting

private theorem blockScalar_lowerBound_withDim {n : Nat}
    {dim height theta : YoungDiagram n -> ℝ} {c : ℝ}
    (htraceScalar : TraceScalarValueInputWithDim dim height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    ∀ lam ∈ nonU1YoungBlocks n, c <= theta lam := by
  classical
  intro lam hlam
  have hnotRow : ¬ IsOneRow lam := (Finset.mem_filter.mp hlam).2.1
  have hnotStandard : ¬ IsStandard lam := (Finset.mem_filter.mp hlam).2.2
  rcases htraceScalar lam with ⟨hdimPos, htheta⟩
  rw [htheta]
  exact (le_div_iff₀ hdimPos).mpr (hcert lam hnotRow hnotStandard)

private theorem spectralGapFromBlockScalars_withDim {n : Nat} (c : ℝ)
    (F : Perm (Fin n) -> ℝ)
    (dim height blockEnergy theta : YoungDiagram n -> ℝ)
    (hdecomp : YoungBlockDecompositionInput blockEnergy)
    (hu1 : U1YoungBlockIdentificationInput F blockEnergy)
    (hscalarity : MatchingAverageScalarityInput F blockEnergy theta)
    (htrace : TraceScalarValueInputWithDim dim height theta)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    c * l2DistSqToU1 F <= matchingMeanProjectionError F := by
  classical
  rw [hu1, hscalarity, Finset.mul_sum]
  exact Finset.sum_le_sum (fun lam hlam => by
    exact mul_le_mul_of_nonneg_right
      (blockScalar_lowerBound_withDim htrace hcert lam hlam)
      (hdecomp lam))

private theorem spectralGapFromBlockModel_withDim {n : Nat}
    (c : ℝ) (dim height : YoungDiagram n -> ℝ)
    (hmodel : SpectralBlockModelInputWithDim dim height)
    (hcert :
      ∀ lam : YoungDiagram n,
        ¬ IsOneRow lam -> ¬ IsStandard lam -> c * dim lam <= height lam) :
    MatchingSpectralGapConstant n c := by
  intro F
  rcases hmodel F with ⟨energy, ⟨scalar⟩⟩
  exact
    spectralGapFromBlockScalars_withDim c F dim height
      energy.blockEnergy scalar.theta energy.nonneg energy.u1_identification
      scalar.scalarity scalar.trace_value hcert

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

/-- Theorem 4.6, `thm:matching-gap`: matching-cube spectral gap.  The active
theorem path uses the tableau-count Section 5 bridge, with Section 5 supplying
the dimension-parameterized spectral-block model input. -/
theorem S04_Thm4_06_MatchingGap
    (n : ℕ) (hn : 4 ≤ n)
    (F : Perm (Fin n) → ℝ) :
    (1 / 6 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F ∧
      (Even n → (1 / 5 : ℝ) * l2DistSqToU1 F ≤ matchingMeanProjectionError F) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases (even_iff_exists_two_mul.mp heven) with ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hgap15 : MatchingSpectralGapConstant (2 * m) (1 / 5 : ℝ) := by
      exact
        spectralGapFromBlockModel_withDim
          (1 / 5 : ℝ)
          (fun lam : YoungDiagram (2 * m) => tableauDim lam)
          (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)
          (spectralBlockModelInputWithDim_even_from_section5 m hm)
          (fun lam hrow hstandard =>
            S05_Lem5_25_tableau_even_certificate m hm lam hrow hstandard)
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
      exact
        spectralGapFromBlockModel_withDim
          (1 / 6 : ℝ)
          (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
          (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
          (spectralBlockModelInputWithDim_odd_from_section5 m hm)
          (fun lam hrow hstandard =>
            S05_Lem5_26_tableau_odd_certificate m hm lam hrow hstandard)
    constructor
    · exact hgap16 F
    · intro heven
      exact False.elim (hnotEven heven)

end DictatorshipTesting
