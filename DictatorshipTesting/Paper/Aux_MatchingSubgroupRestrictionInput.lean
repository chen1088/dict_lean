import DictatorshipTesting.Paper.Aux_MatchingRestrictionInput

/-!
# Matching-subgroup restriction input

Compatibility names for the matching-restriction input.  New code should import
`Aux_MatchingRestrictionInput`; these names remain so earlier scaffold files do
not have to move all at once.
-/

noncomputable section

namespace DictatorshipTesting

/-- Compatibility alias for `MatchingRestrictionEvenInput`. -/
abbrev MatchingSubgroupRestrictionEvenInput (m : ℕ) : Prop :=
  MatchingRestrictionEvenInput m

/-- Compatibility alias for `MatchingRestrictionOddInput`. -/
abbrev MatchingSubgroupRestrictionOddInput (m : ℕ) : Prop :=
  MatchingRestrictionOddInput m

/-- Compatibility wrapper for the even matching-restriction input. -/
theorem matchingSubgroupRestriction_even_specht_pieri_input (m : ℕ) :
    MatchingSubgroupRestrictionEvenInput m := by
  exact matchingRestriction_even_specht_pieri_input m

/-- Compatibility wrapper for the odd matching-restriction input. -/
theorem matchingSubgroupRestriction_odd_specht_pieri_input (m : ℕ) :
    MatchingSubgroupRestrictionOddInput m := by
  exact matchingRestriction_odd_specht_pieri_input m

end DictatorshipTesting
