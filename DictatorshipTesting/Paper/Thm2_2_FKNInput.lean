import DictatorshipTesting.Paper.Aux_FKNStabilityInput

/-!
# Theorem 2.2: FKN/stability input on `Sₙ`

This is the paper's imported stability theorem, `thm:fkn-input`.
-/

namespace DictatorshipTesting

/-- Theorem 2.2, `thm:fkn-input`: distance from `U₁` controls dictator distance. -/
theorem Thm2_2_FKNInput :
    ∃ cFKN : ℝ, 0 < cFKN ∧
      ∀ n : ℕ, ∀ f : BoolFn (Fin n),
        cFKN * (distToDictators f) ^ (2 : ℕ) ≤
          l2DistSqToU1 (boolFnToReal f) := by
  exact fknStability_input

end DictatorshipTesting
