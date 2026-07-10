import DictatorshipTesting.Paper.S05_Lem5_10_MatchingSubgroupEigenbasis
import DictatorshipTesting.Paper.Defs.S05_Def5_20_TraceLocalTruncationEvenInput
import DictatorshipTesting.Paper.Defs.S05_Def5_21_TraceLocalTruncationOddInput
import DictatorshipTesting.Paper.Defs.S05_Def5_30_TableauOperatorTrace

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_16_BlockScalarOfTheAveragedRejection`
-/


/-!
Paper statement: Lemma 5.12 (`lem:PM-trace-young-block`)
Title in paper: Trace of one local truncation on one Young block.

Status: unproven as the paper's numerical fixed-trace statement.  The concrete
operator is reduced below to its character-idempotent traces, and the full
matrix-coordinate trace factor is proved.  The missing step is the actual
matching eigenbasis with its sign-pattern multiplicities.
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

/-- Concrete operator reduction for Lemma 5.12: the fixed high-matching trace
is the sum of the traces of its high-character Fourier idempotents. -/
theorem S05_Lem5_12_fixedMatching_trace_eq_sum_characterTraces
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    tableauOperatorTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
        tableauOperatorTrace
          (S05_fixedMatchingCharacterYoungOperator action M R) := by
  exact S05_fixedMatchingRejectionYoungOperator_trace_eq_sum_characters
    action M

/-- Concrete multiplicity reduction for Lemma 5.12: right action on the full
matrix-coordinate Young block contributes one identical trace for each left
tableau index. -/
theorem S05_Lem5_12_youngBlockTrace_eq_tableauDim_mul_repTrace
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    youngBlockRightCoordinateTrace
        (S05_fixedMatchingRejectionYoungOperator action M) =
      tableauDim lam *
        tableauOperatorTrace
          (S05_fixedMatchingRejectionYoungOperator action M) := by
  exact fixedMatchingYoungBlockTrace_eq_tableauDim_mul_repTrace action M

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
