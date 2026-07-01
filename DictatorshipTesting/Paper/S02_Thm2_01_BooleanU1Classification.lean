import DictatorshipTesting.Paper.Defs

/-!
# Structural input for Theorem 2.1

This file isolates the external classification theorem used by the paper:
Boolean functions in the first permutation module are dictators.
-/

namespace DictatorshipTesting

/-- External structural input behind Theorem 2.1. -/
theorem booleanU1_iff_dictator_input (n : ℕ) (f : BoolFn (Fin n)) :
    boolFnToReal f ∈ U1 (Fin n) ↔ IsDictator f := by
  sorry

end DictatorshipTesting
