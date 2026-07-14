import DictatorshipTesting.SetFacts

/-
Direct reverse imports:
- `DictatorshipTesting`
-/
namespace DictatorshipTesting

variable {α : Type*}

/-- Lean version of Fact `ft:sub_sd` from the paper. -/
theorem setMinus_symmDiff
    (L M R : Set α) :
    ((L \ₛ M) △ R) =
      (L \ₛ (M ∪ R)) ∪ (R \ₛ L) ∪ (L ∩ M ∩ R) := by
  ext x
  unfold setMinus symmDiff
  by_cases hL : x ∈ L <;>
  by_cases hM : x ∈ M <;>
  by_cases hR : x ∈ R <;>
  simp [hL, hM, hR]

end DictatorshipTesting
