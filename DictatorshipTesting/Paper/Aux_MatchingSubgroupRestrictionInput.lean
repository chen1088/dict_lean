import DictatorshipTesting.Paper.Defs

/-!
# Matching-subgroup restriction input

This file isolates the Specht-module/Pieri part of the Section 5 bridge.  The
full mathematical statement is that restricting the Specht module `S^lambda` to
the matching subgroup `A_M` decomposes with local character weights recorded by
the multiset `X_m(lambda)`.

The current Lean vocabulary does not yet contain Specht modules or their
restriction functor.  The formal statements below therefore record the
numerical shadow of that restriction data that is visible in the current
development: the high-weight multiplicities counted by `hEven` and `hOdd` are
valid multiplicities inside a block of dimension `youngDim`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Even Specht/Pieri restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingSubgroupRestrictionEvenInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m),
    0 ≤ hEven m lam ∧ hEven m lam ≤ youngDim lam

/-- Odd Specht/Pieri restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingSubgroupRestrictionOddInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m + 1),
    0 ≤ hOdd m lam ∧ hOdd m lam ≤ youngDim lam

/-- Standard representation-theoretic input: the even matching-subgroup
restriction realizes the multiset counted by `hEven`. -/
theorem matchingSubgroupRestriction_even_specht_pieri_input (m : ℕ) :
    MatchingSubgroupRestrictionEvenInput m := by
  sorry

/-- Standard representation-theoretic input: the odd matching-subgroup
restriction realizes the multiset counted by `hOdd`. -/
theorem matchingSubgroupRestriction_odd_specht_pieri_input (m : ℕ) :
    MatchingSubgroupRestrictionOddInput m := by
  sorry

end DictatorshipTesting
