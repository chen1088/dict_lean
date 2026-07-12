import DictatorshipTesting.Paper.S05_Int_DegreeOneYoungBlock

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition`
-/


/-!
Paper statement: Lemma 5.12 (`lem:degree-one-young-blocks`)
Title in paper: Degree-one Young-block identification.

Status: proven internally.  The theorem below identifies `U1` with the
concrete one-row plus standard matrix-coefficient blocks.  The numerical
distance identity is derived later from this equality and the internal
orthogonal decomposition.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.12: degree-one Young-block identification, proved through the
explicit permutation-coordinate decomposition. -/
theorem S05_Lem5_12_degreeOneYoungBlockIdentification
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action := by
  exact U1_eq_concreteDegreeOneYoungBlockSum action

end DictatorshipTesting
