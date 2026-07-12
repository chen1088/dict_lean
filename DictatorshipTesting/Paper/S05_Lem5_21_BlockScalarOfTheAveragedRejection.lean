import DictatorshipTesting.Paper.S05_Lem5_18_TraceOfOneLocalTruncationOnOneYoungBlock
import DictatorshipTesting.Paper.S05_Lem5_08_YoungBasisScalarCommutant
import DictatorshipTesting.Paper.S05_Lem5_20_CentralAveragedRejection
import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_22_GlobalWeightedMatchingIdentity`
-/


/-!
Paper statement: Lemma 5.21 (`lem:centralization-matchings`)
Title in paper: Block scalar of the averaged rejection.

Status: proven.  This file proves the finite-dimensional
trace-divided-by-dimension algebra. Lemma 5.22 proves the concrete block action
and the resulting global weighted matching identity.
-/

/-!
# Centralization bridge

The paper's centralization step has one part that is ordinary algebra once
scalarity and the trace identity are known:

`theta = tr(A|H_lambda) / dim(H_lambda) = h_m(lambda) / d_lambda`.

That trace-divided-by-dimension calculation is proved here.  The concrete
Young-block scalar action and its global orthogonal assembly are proved in
Lemma 5.22 from the faithful Section 5 interfaces.
-/

noncomputable section

namespace DictatorshipTesting

/-- If a scalar operator on a block of dimension `d^2` has trace `d * h`, then
its scalar is `h / d`.  This is the trace-divided-by-dimension calculation in
the centralization lemma. -/
theorem scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  have hd2 : d ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hd
  calc
    theta = (d ^ (2 : ℕ) * theta) / d ^ (2 : ℕ) := by
      field_simp [hd2]
    _ = (d * h) / d ^ (2 : ℕ) := by
      rw [htrace]
    _ = h / d := by
      field_simp [hd]

/-- Even Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem even_youngBlockScalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact scalar_eq_trace_div_dimension
    (youngDim lam) (hEven m lam) theta hdim htrace

/-- Odd Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem odd_youngBlockScalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact scalar_eq_trace_div_dimension
    (youngDim lam) (hOdd m lam) theta hdim htrace

/-- Centralization scalar algebra: if a scalar operator on a block of dimension
`d^2` has trace `d * h`, then the scalar is `h / d`. -/
theorem centralizationBridge_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact scalar_eq_trace_div_dimension d h theta hd htrace

/-- Even Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem centralizationBridge_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact even_youngBlockScalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Odd Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem centralizationBridge_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact odd_youngBlockScalar_eq_hOdd_div_dim m lam theta hdim htrace

/-- Lemma 5.21 paper-numbered scalar algebra: trace divided by dimension. -/
theorem S05_Lem5_21_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact centralizationBridge_scalar_eq_trace_div_dimension d h theta hd htrace

/-- Lemma 5.21 paper-numbered even scalar formula. -/
theorem S05_Lem5_21_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact centralizationBridge_even_scalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Lemma 5.21 paper-numbered odd scalar formula. -/
theorem S05_Lem5_21_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact centralizationBridge_odd_scalar_eq_hOdd_div_dim m lam theta hdim htrace


/-- In even size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension.  This uses the
completed internal fixed-trace theorem rather than the global Theorem 5.5 trace
payload. -/
theorem averagedHigh_youngBlockScalar_even
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content)).basisScalar T0 =
      hEvenTableau (m + 1) lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_18_fixedMatching_tableauTrace_even m lam action]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  have hcard :
      (Fintype.card (NearPerfectMatching (2 * (m + 1))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [Nat.mul_add]

/-- In odd size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension. -/
theorem averagedHigh_youngBlockScalar_odd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content)).basisScalar T0 =
      hOddTableau m lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_18_fixedMatching_tableauTrace_odd m lam action]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  have hcard :
      (Fintype.card (NearPerfectMatching (2 * m + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp


end DictatorshipTesting
