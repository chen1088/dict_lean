/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_08_RegularYoungBlockDecomposition`
-/
import AlgebraicLibrary.Young.TableauSumOfSquares
import AlgebraicLibrary.Young.DiagramCorners

open AlgebraicLibrary

/-!
Paper statement: Lemma 5.7 (`lem:young-tableau-sum-of-squares`).
-/

namespace DictatorshipTesting

theorem S05_Lem5_07_youngTableau_sum_of_squares (n : Nat) :
    (Finset.univ.sum fun lam : YoungDiagram n =>
      tableauDimNat lam ^ 2) = n.factorial :=
  sum_tableauDimNat_sq_eq_factorial n

end DictatorshipTesting
