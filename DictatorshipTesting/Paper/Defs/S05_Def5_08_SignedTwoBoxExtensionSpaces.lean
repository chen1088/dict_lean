/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Lem5_20_MatchingSubgroupEigenbasis

/-!
Paper statement: Definition 5.8 `def:signed-two-box-extension-spaces`
Title in paper: Signed two-box extension spaces.

The underlying coordinate constructions are shared with the recursive matching
eigenbasis proof and are re-exported here under the paper definition number.
-/

namespace DictatorshipTesting

noncomputable def S05_Def5_08_signedTwoBoxExtensionBasisVector :=
  @S05_signedTwoBoxExtensionBasisVector

noncomputable def S05_Def5_08_signedTwoBoxChildEmbedding :=
  @S05_signedTwoBoxChildEmbedding

abbrev S05_Def5_08_SignedTwoBoxBasisIndex
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :=
  S05_SignedTwoBoxBasisIndex lam

end DictatorshipTesting
