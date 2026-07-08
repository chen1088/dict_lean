import DictatorshipTesting.Basic

/-
Direct reverse imports (generated):
- `DictatorshipTesting.BasicFacts`
-/

namespace DictatorshipTesting

variable {α : Type*} [DecidableEq α]

@[simp] theorem pswap_self_right (a b : α) : pswap a b b = a := by
  simp [pswap]

end DictatorshipTesting
