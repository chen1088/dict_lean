import Mathlib

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.SetFacts.Fact_sub_sd_SetMinusSymmDiff`
-/
/-!
# Set identities used in `dict.tex`

This file formalizes the elementary set identity labelled `ft:sub_sd` in the
paper:

  (L \ M) Δ R = (L \ (M ∪ R)) ∪ (R \ L) ∪ (L ∩ M ∩ R).

We define our own symmetric-difference notation so that the statement does not
depend on a particular Mathlib notation for symmetric difference.
-/

namespace DictatorshipTesting

variable {α : Type*}

/-- Set-theoretic difference, written as a named definition for local notation. -/
def setMinus (A B : Set α) : Set α := {x | x ∈ A ∧ x ∉ B}

/-- Symmetric difference of two sets. -/
def symmDiff (A B : Set α) : Set α :=
  {x | (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)}

infixl:70 " \\ₛ " => setMinus
infixl:65 " △ " => symmDiff

end DictatorshipTesting
