import DictatorshipTesting.Paper.Aux_YoungMatchingOperators
import DictatorshipTesting.Paper.S05_Lem5_36_OddCertificate

/-!
Paper statement: Lemma 5.19 (`lem:matching-restriction-X`)
Title in paper: Matching subgroup eigenbasis.

Legacy scalar-shadow file for the rewritten Section 5 statement.

Status: the paper's Lemma 5.19 is the full Specht-module restriction statement
obtained from repeated Pieri/Littlewood--Richardson branching.  The current
Lean file does not formalize Specht modules or restriction functors; it proves
only the scalar/multiplicity shadow used downstream by the scaffold.
-/

/-!
# Matching-restriction scalar shadow

The paper's full statement says that, after restricting the Specht module
indexed by `lambda` to the matching subgroup `A_M ≃ (Z / 2Z)^m`, the local
character-weight multiset is the recursively defined multiset counted by
`zEven`, `hEven`, and `hOdd`.

The current Lean vocabulary does not yet contain Specht modules or restriction
functors.  The statements below therefore do not claim to be the full
restriction theorem.  They record the scalar bounds needed by the rest of the
scaffold, and those scalar consequences are proved from the finite certificate
bounds already formalized.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.19 matching-operator component: a canonical even matching edge
operator is an involution. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorEven_involutive
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven r f) = f := by
  exact canonicalMatchingYoungOperatorEven_involutive r f

/-- Lemma 5.19 matching-operator component: distinct canonical even matching
edge operators commute. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorEven_comm
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven s f) =
      canonicalMatchingYoungOperatorEven s
        (canonicalMatchingYoungOperatorEven r f) := by
  exact canonicalMatchingYoungOperatorEven_comm hrs f

/-- Lemma 5.19 matching-operator component: a canonical odd matching edge
operator is an involution. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorOdd_involutive
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd r f) = f := by
  exact canonicalMatchingYoungOperatorOdd_involutive r f

/-- Lemma 5.19 matching-operator component: distinct canonical odd matching
edge operators commute. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorOdd_comm
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd s f) =
      canonicalMatchingYoungOperatorOdd s
        (canonicalMatchingYoungOperatorOdd r f) := by
  exact canonicalMatchingYoungOperatorOdd_comm hrs f

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

/-- Scalar consequence for even matching subgroups. -/
theorem matchingRestriction_even_specht_pieri_input
    [TwoStripDimensionBranchingAssumption] (m : ℕ) :
    MatchingRestrictionEvenInput m := by
  intro lam
  exact ⟨hEven_nonneg m lam, hEven_le_youngDim m lam⟩

/-- Scalar consequence for odd matching subgroups. -/
theorem matchingRestriction_odd_specht_pieri_input
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption] (m : ℕ) :
    MatchingRestrictionOddInput m := by
  intro lam
  exact ⟨hOdd_nonneg m lam, hOdd_le_youngDim m lam⟩

end DictatorshipTesting
