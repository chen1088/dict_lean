import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Theorem 2.2 (`thm:fkn-input`)
Title in paper: FKN/stability input on S_n.

Status: external: Filmus FKN/stability theorem.
-/

/-!
# Stability input for Theorem 2.2

This file isolates the imported FKN/stability theorem used by the active
soundness proof.  Lemma 4.13 consumes exactly the wrapper `Thm2_2_FKNInput`.
-/

namespace DictatorshipTesting

/-- External FKN/stability input behind Theorem 2.2.

Reference: Filmus, *Boolean functions on `S_n` which are nearly linear*,
Discrete Analysis 2021:25, Theorem 1.5, combined with the Boolean `U₁`
classification in Theorem 2.8 and the standard reduction recorded in the paper
around `thm:fkn-input`. -/
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
