import DictatorshipTesting.Paper.S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock
import DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum
import DictatorshipTesting.Paper.AppA_LemA_04_StandardTableauxSwapConnectedness

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_SpectralBridgeAlgebra`
- `DictatorshipTesting.Paper.S05_Int_SpectralBridgeFromCertificates`
-/


/-!
Paper statement: Lemma 5.16 (`lem:centralization-matchings`)
Title in paper: Block scalar of the averaged rejection.

Status: external: Section 5 scalarity bridge input.  Finite-dimensional
trace-divided-by-dimension algebra is proved here; matching-average scalarity is
isolated as `S05_matchingAverageScalarity_from_young_model_input`.
-/

/-!
# Centralization bridge

The paper's centralization step has one part that is ordinary algebra once
scalarity and the trace identity are known:

`theta = tr(A|H_lambda) / dim(H_lambda) = h_m(lambda) / d_lambda`.

That trace-divided-by-dimension calculation is proved here.  The
representation-theoretic claim that the averaged operator is scalar on each
Young block still belongs to the final spectral-decomposition input.
-/

noncomputable section

namespace DictatorshipTesting

/-- Section 5 scalarity bridge input.  Given the Appendix A.4 connectedness
statement and the trace/scalar data from the Young model, the averaged matching
rejection is scalar on each Young block with scalar `theta`. -/
def S05_MatchingAverageScalarityFromYoungModelStatement : Prop :=
  AppA_LemA_04_StandardTableauxSwapConnectednessStatement ->
  ∀ {n : Nat} {dim height : YoungDiagram n -> ℝ}
    {F : Perm (Fin n) -> ℝ}
    {energy : AppA_YoungBlockEnergyData F}
    (traceData : AppA_TraceScalarDataWithDim dim height energy),
    MatchingAverageScalarityInput F energy.blockEnergy traceData.theta

/-- Section 5 input isolating the still-external bridge from the Young-model
connectedness and trace data to matching-average scalarity. -/
axiom S05_matchingAverageScalarity_from_young_model_input :
    S05_MatchingAverageScalarityFromYoungModelStatement

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

/-- Lemma 5.11 paper-numbered scalar algebra: trace divided by dimension. -/
theorem S05_Lem5_16_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact centralizationBridge_scalar_eq_trace_div_dimension d h theta hd htrace

/-- Lemma 5.11 paper-numbered even scalar formula. -/
theorem S05_Lem5_16_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact centralizationBridge_even_scalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Lemma 5.11 paper-numbered odd scalar formula. -/
theorem S05_Lem5_16_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact centralizationBridge_odd_scalar_eq_hOdd_div_dim m lam theta hdim htrace

end DictatorshipTesting
