import DictatorshipTesting.Paper.Aux_YoungMatchingOperators

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_23_MatchingSubgroupEigenbasis`
-/

/-!
Paper statement: Lemma 5.23 (`lem:matching-restriction-X`), odd eigenvector
component.
Title in paper: Matching subgroup eigenbasis.

Status: definition/interface. This names the simultaneous odd matching-edge
eigenvector predicate used by the matching-character wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.23 matching-character component: simultaneous odd matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorOdd f R

end DictatorshipTesting
