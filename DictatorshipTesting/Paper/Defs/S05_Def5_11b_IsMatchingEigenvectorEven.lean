import DictatorshipTesting.Paper.S05_Int_YoungMatchingOperators

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_20_MatchingSubgroupEigenbasis`
-/

/-!
Paper statement: Definition 5.11 part (b) `def:matching-characters-and-eigenvectors`
Title in paper: Matching characters and eigenvectors.

Status: definition/interface. This names the simultaneous even matching-edge
eigenvector predicate used by the matching-character wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.11 matching-character component: simultaneous even matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorEven f R

end DictatorshipTesting
