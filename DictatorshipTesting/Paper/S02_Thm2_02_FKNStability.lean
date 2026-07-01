import DictatorshipTesting.Paper.Defs

/-!
# Stability input for Theorem 2.2

This file isolates the imported FKN/stability theorem used by the paper.
-/

namespace DictatorshipTesting

/-- External FKN/stability input behind Theorem 2.2. -/
theorem fknStability_input :
    ∃ cFKN : ℝ, 0 < cFKN ∧
      ∀ n : ℕ, ∀ f : BoolFn (Fin n),
        cFKN * (distToDictators f) ^ (2 : ℕ) ≤
          l2DistSqToU1 (boolFnToReal f) := by
  sorry

end DictatorshipTesting
