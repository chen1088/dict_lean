import DictatorshipTesting.Paper.Aux_CentralizationOverMatchings

/-!
Paper statement: Lemma 5.30 (`lem:centralization-matchings`)
Title in paper: Block scalar of the averaged rejection.

Status: external: trace/scalar model input. Finite-dimensional trace-divided-by-dimension algebra is proved in the
helper imported here; the remaining Young-block scalarity belongs to the
spectral bridge input.
-/

/-!
# Centralization bridge

The paper's centralization step has one part that is ordinary algebra once
scalarity and the trace identity are known:

`theta = tr(A|H_lambda) / dim(H_lambda) = h_m(lambda) / d_lambda`.

That trace-divided-by-dimension calculation is proved here through the existing
`Aux_CentralizationOverMatchings` lemmas.  The representation-theoretic claim
that the averaged operator is scalar on each Young block still belongs to the
final spectral-decomposition input.
-/

noncomputable section

namespace DictatorshipTesting

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

/-- Lemma 5.30 paper-numbered scalar algebra: trace divided by dimension. -/
theorem S05_Lem5_30_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact centralizationBridge_scalar_eq_trace_div_dimension d h theta hd htrace

/-- Lemma 5.30 paper-numbered even scalar formula. -/
theorem S05_Lem5_30_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact centralizationBridge_even_scalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Lemma 5.30 paper-numbered odd scalar formula. -/
theorem S05_Lem5_30_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact centralizationBridge_odd_scalar_eq_hOdd_div_dim m lam theta hdim htrace

end DictatorshipTesting
