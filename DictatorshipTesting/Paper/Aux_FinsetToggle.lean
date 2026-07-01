import DictatorshipTesting.Paper.Defs

namespace DictatorshipTesting

/-- Toggle membership of one element in a finset. -/
def finsetToggle {α : Type*} [DecidableEq α] (a : α) (S : Finset α) : Finset α :=
  if a ∈ S then S.erase a else insert a S

end DictatorshipTesting
