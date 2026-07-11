/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Int_AdjacentCoxeterPresentation

/-!
Paper statement: Lemma 5.2 (`lem:type-A-adjacent-word-presentation`).
-/

namespace DictatorshipTesting

/-- Two adjacent words represent the same permutation exactly when the
type-A Coxeter moves connect them. -/
theorem S05_Lem5_02_typeA_adjacentWord_presentation
    {n : Nat} {w v : AdjacentWord n} :
    adjacentWordPerm w = adjacentWordPerm v ↔
      AdjacentWord.CoxeterEquiv w v := by
  constructor
  · exact adjacentWordPerm_complete
  · exact adjacentWordPerm_respects_coxeter_equiv

end DictatorshipTesting
