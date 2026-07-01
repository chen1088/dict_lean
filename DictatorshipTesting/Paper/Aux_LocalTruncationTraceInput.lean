import DictatorshipTesting.Paper.Aux_TraceLocalTruncation
import DictatorshipTesting.Paper.Aux_MatchingSubgroupRestrictionInput

/-!
# Trace of one local truncation

Compatibility names for the trace-local-truncation input.  New code should
import `Aux_TraceLocalTruncation`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Compatibility alias for `TraceLocalTruncationEvenInput`. -/
abbrev LocalTruncationTraceEvenInput (m : ℕ) : Prop :=
  TraceLocalTruncationEvenInput m

/-- Compatibility alias for `TraceLocalTruncationOddInput`. -/
abbrev LocalTruncationTraceOddInput (m : ℕ) : Prop :=
  TraceLocalTruncationOddInput m

/-- Compatibility wrapper for the even trace formula. -/
theorem localTruncationTrace_even_from_restriction
    (m : ℕ) (hrestrict : MatchingSubgroupRestrictionEvenInput m) :
    LocalTruncationTraceEvenInput m := by
  exact traceLocalTruncation_even_from_restriction m hrestrict

/-- Compatibility wrapper for the odd trace formula. -/
theorem localTruncationTrace_odd_from_restriction
    (m : ℕ) (hrestrict : MatchingSubgroupRestrictionOddInput m) :
    LocalTruncationTraceOddInput m := by
  exact traceLocalTruncation_odd_from_restriction m hrestrict

end DictatorshipTesting
