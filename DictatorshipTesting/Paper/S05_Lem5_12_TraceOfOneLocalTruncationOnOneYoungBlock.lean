import DictatorshipTesting.Paper.S05_Lem5_10_MatchingSubgroupEigenbasis
import DictatorshipTesting.Paper.Defs.S05_Def5_20_TraceLocalTruncationEvenInput
import DictatorshipTesting.Paper.Defs.S05_Def5_21_TraceLocalTruncationOddInput

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_16_BlockScalarOfTheAveragedRejection`
-/


/-!
Paper statement: Lemma 5.12 (`lem:PM-trace-young-block`)
Title in paper: Trace of one local truncation on one Young block.

Status: external: block trace model input. Derived from the matching-restriction input and finite scalar
certificate definitions.
-/

/-!
# Trace of one local truncation

Assuming the matching-restriction data, the trace of `I - P_M` on a Young block
is obtained by counting high-weight matching characters.  The paper's factor is

`tr((I - P_M)|_{H_lambda}) = d_lambda * h_m(lambda)`.

The extra factor `d_lambda` comes from the block
`H_lambda ≃ S^lambda ⊗ (S^lambda)^*`: the restricted Specht multiplicities occur
in `d_lambda` matrix-coefficient copies.  The current Lean vocabulary does not
yet contain these Young blocks as vector spaces, so this file records the
scalar trace formula used by the later bridge.
-/

noncomputable section

namespace DictatorshipTesting

/-- Scalar trace formula as the current Lean consequence of the even
matching-restriction input. -/
theorem traceLocalTruncation_even_from_restriction
    (m : ℕ) (_hrestrict : MatchingRestrictionEvenInput m) :
    TraceLocalTruncationEvenInput m := by
  intro lam
  exact ⟨youngDim lam * hEven m lam, rfl⟩

/-- Scalar trace formula as the current Lean consequence of the odd
matching-restriction input. -/
theorem traceLocalTruncation_odd_from_restriction
    (m : ℕ) (_hrestrict : MatchingRestrictionOddInput m) :
    TraceLocalTruncationOddInput m := by
  intro lam
  exact ⟨youngDim lam * hOdd m lam, rfl⟩

end DictatorshipTesting
