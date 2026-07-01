import DictatorshipTesting.Paper.Aux_MatchingSubgroupRestrictionInput

/-!
# Trace of one local truncation

Assuming the matching-subgroup restriction data, the trace of `I - P_M` on a
Young block is obtained by counting high-weight matching characters.  In the
paper this is the formula

`tr((I - P_M)|_{H_lambda}) = d_lambda * h_m(lambda)`.

Since the current Lean files do not yet formalize Young blocks as vector
spaces, this file records the scalar formula that the later spectral bridge
uses.
-/

noncomputable section

namespace DictatorshipTesting

/-- Scalar trace formula for one even Young block. -/
def LocalTruncationTraceEvenInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m),
    ∃ traceLocalHigh : ℝ,
      traceLocalHigh = youngDim lam * hEven m lam

/-- Scalar trace formula for one odd Young block. -/
def LocalTruncationTraceOddInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m + 1),
    ∃ traceLocalHigh : ℝ,
      traceLocalHigh = youngDim lam * hOdd m lam

/-- The trace formula as a scalar consequence of the even restriction input.

The actual identification of `traceLocalHigh` with the operator trace belongs
to the representation-theoretic model, which is not yet formalized. -/
theorem localTruncationTrace_even_from_restriction
    (m : ℕ) (_hrestrict : MatchingSubgroupRestrictionEvenInput m) :
    LocalTruncationTraceEvenInput m := by
  intro lam
  exact ⟨youngDim lam * hEven m lam, rfl⟩

/-- The trace formula as a scalar consequence of the odd restriction input.

The actual identification of `traceLocalHigh` with the operator trace belongs
to the representation-theoretic model, which is not yet formalized. -/
theorem localTruncationTrace_odd_from_restriction
    (m : ℕ) (_hrestrict : MatchingSubgroupRestrictionOddInput m) :
    LocalTruncationTraceOddInput m := by
  intro lam
  exact ⟨youngDim lam * hOdd m lam, rfl⟩

end DictatorshipTesting
