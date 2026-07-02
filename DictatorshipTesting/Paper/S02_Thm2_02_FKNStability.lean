import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Theorem 2.2 (`thm:fkn-input`)
Title in paper: FKN/stability input on S_n.

Status: external structural input from Filmus's FKN/stability theorem.
-/

/-!
# Stability input for Theorem 2.2

This file isolates the imported FKN/stability theorem used by the paper.
-/

namespace DictatorshipTesting

/-- External FKN/stability input behind Theorem 2.2. -/
theorem fknStability_input :
    ∃ cFKN : ℝ, 0 < cFKN ∧
      ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
        cFKN * (distToDictators f) ^ (2 : ℕ) ≤
          l2DistSqToU1 (boolFnToReal f) := by
  sorry

/-- Theorem 2.2, `thm:fkn-input`: imported FKN/stability input.  This preserves
the old theorem name while keeping the assumption in the paper-numbered file. -/
theorem Thm2_2_FKNInput :
    ∃ cFKN : ℝ, 0 < cFKN ∧
      ∀ n : ℕ, 4 ≤ n → ∀ f : BoolFn (Fin n),
        cFKN * (distToDictators f) ^ (2 : ℕ) ≤
          l2DistSqToU1 (boolFnToReal f) := by
  exact fknStability_input

end DictatorshipTesting
