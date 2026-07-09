import DictatorshipTesting.Paper.Aux_YoungMatchingOperators

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_23_MatchingSubgroupEigenbasis`
-/

/-!
Paper statement: Lemma 5.23 (`lem:matching-restriction-X`), even eigenvector
component.
Title in paper: Matching subgroup eigenbasis.

Status: definition/interface. This names the simultaneous even matching-edge
eigenvector predicate used by the matching-character wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.23 matching-character component: simultaneous even matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorEven f R

end DictatorshipTesting
