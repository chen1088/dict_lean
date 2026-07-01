import DictatorshipTesting.Basic

namespace DictatorshipTesting

/-- Multiplication of two `{0,1}` indicators is the indicator of conjunction. -/
lemma natIndicator_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : ℕ) * (if Q then 1 else 0 : ℕ)) =
      (if P ∧ Q then 1 else 0 : ℕ) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

end DictatorshipTesting
