import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauEvenHeight

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Int_SignPatternCardinalities`
- `DictatorshipTesting.Paper.S05_Lem5_16_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Lem5_22_GlobalWeightedMatchingIdentity`
- `DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate`
-/

/-!
Definition file for `hOddTableau`.

This neutral height function is used both by the finite certificate proof and by
the Section 5 spectral-model interface.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Odd high-weight count using actual tableau dimensions in the even
children. -/
noncomputable def hOddTableau (m : Nat) (lam : YoungDiagram (2 * m + 1)) : Real :=
  (oneBoxChildrenOdd m lam).sum (fun mu => hEvenTableau m mu)

end DictatorshipTesting
