import DictatorshipTesting.Paper.Defs

/-!
# Matching-restriction input

This file isolates the representation-theoretic input from Section 5: after
restricting the Specht module indexed by `lambda` to the matching subgroup
`A_M ≃ (Z / 2Z)^m`, the local character-weight multiset is the recursively
defined multiset counted by `zEven`, `hEven`, and `hOdd`.

The current Lean vocabulary does not yet contain Specht modules or restriction
functors.  The statements below therefore record the numerical shadow of that
restriction theorem that the rest of the scaffold can currently use.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionEvenInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m),
    0 ≤ hEven m lam ∧ hEven m lam ≤ youngDim lam

/-- Odd matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionOddInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m + 1),
    0 ≤ hOdd m lam ∧ hOdd m lam ≤ youngDim lam

/-- Standard Specht/Pieri-Littlewood-Richardson input for even matching
subgroups. -/
theorem matchingRestriction_even_specht_pieri_input (m : ℕ) :
    MatchingRestrictionEvenInput m := by
  sorry

/-- Standard Specht/Pieri-Littlewood-Richardson input for odd matching
subgroups, with the one unmatched point handled by ordinary branching. -/
theorem matchingRestriction_odd_specht_pieri_input (m : ℕ) :
    MatchingRestrictionOddInput m := by
  sorry

end DictatorshipTesting
