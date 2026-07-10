import DictatorshipTesting.Paper.S05_Int_YoungMatchingOperators

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_11_MatchingSubgroupEigenbasis`
-/

/-!
Paper statement: Definition 5.17 (`def:odd-matching-eigenvector`).
Title in paper: Odd matching eigenvector predicate.

Status: definition/interface. This names the simultaneous odd matching-edge
eigenvector predicate used by the matching-character wrappers.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.17 matching-character component: simultaneous odd matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorOdd f R

end DictatorshipTesting
