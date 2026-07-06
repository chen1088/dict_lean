import DictatorshipTesting.Paper.S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock

/-!
# Centralization over matchings

The representation-theoretic statement in the paper has two parts:

1. averaging over matchings gives an operator that is central and therefore
   scalar on each Young block by Schur's lemma;
2. once scalarity and the trace formula are known, the scalar is trace divided
   by the block dimension.

The first part still needs Young blocks and group actions in Lean.  The second
part is ordinary scalar algebra and is proved here.
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

end DictatorshipTesting
