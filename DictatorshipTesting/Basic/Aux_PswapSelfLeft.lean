import DictatorshipTesting.Basic

namespace DictatorshipTesting

variable {α : Type*} [DecidableEq α]

@[simp] theorem pswap_self_left (a b : α) : pswap a b a = b := by
  simp [pswap]

end DictatorshipTesting
