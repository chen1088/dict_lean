/-
Direct reverse imports:
- `DictatorshipTesting`
-/

import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition

/-!
Paper statement: Definition 5.6 part (b) `def:young-block`
Title in paper: Young matrix coefficients, blocks, and energies.
-/

namespace DictatorshipTesting

abbrev S05_Def5_06b_YoungMatrixCoefficientIndex :=
  YoungMatrixCoefficientIndex

noncomputable def S05_Def5_06b_globalYoungMatrixCoefficient :=
  @globalYoungMatrixCoefficient

end DictatorshipTesting
