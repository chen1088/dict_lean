/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_11_RegularYoungBlockDecomposition`
-/

import DictatorshipTesting.Paper.S05_Int_YoungTableauSumOfSquares
import DictatorshipTesting.Paper.Defs.S05_Def5_07a_TwoBoxRemovals

/-!
Paper statement: Lemma 5.10 (`lem:young-tableau-sum-of-squares`).
-/

namespace DictatorshipTesting

theorem S05_Lem5_10_youngTableau_sum_of_squares (n : Nat) :
    (Finset.univ.sum fun lam : YoungDiagram n =>
      tableauDimNat lam ^ 2) = n.factorial :=
  sum_tableauDimNat_sq_eq_factorial n

end DictatorshipTesting
