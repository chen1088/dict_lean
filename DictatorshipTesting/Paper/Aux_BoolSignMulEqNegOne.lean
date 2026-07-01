import DictatorshipTesting.Paper.Defs

namespace DictatorshipTesting

/-- Distinct Boolean bits have opposite `{1,-1}` signs. -/
theorem boolSign_mul_eq_neg_one_of_ne {a b : Bool} (h : a ≠ b) :
    ((if a then (-1 : ℝ) else 1) * (if b then (-1 : ℝ) else 1)) = -1 := by
  cases a <;> cases b <;> simp at h ⊢

end DictatorshipTesting
