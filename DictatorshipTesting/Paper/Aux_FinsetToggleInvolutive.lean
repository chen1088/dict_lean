import DictatorshipTesting.Paper.Aux_FinsetToggle

namespace DictatorshipTesting

/-- Toggling the same finset element twice is the identity. -/
theorem finsetToggle_involutive {α : Type*} [DecidableEq α] (a : α) (S : Finset α) :
    finsetToggle a (finsetToggle a S) = S := by
  by_cases h : a ∈ S <;> simp [finsetToggle, h]

end DictatorshipTesting
