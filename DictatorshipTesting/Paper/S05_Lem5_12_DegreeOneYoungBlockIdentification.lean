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

/-- Faithful Lemma 5.12 statement: for every supplied Young orthogonal action,
`U_1` is exactly the concrete sum of the one-row and standard `(n-1,1)`
matrix-coefficient blocks. -/
def S05_Lem5_12_DegreeOneYoungBlockIdentificationStatement : Prop :=
  ∀ {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam),
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action

/-- Lemma 5.12: degree-one Young-block identification, proved through the
explicit permutation-coordinate decomposition. -/
theorem S05_Lem5_12_degreeOneYoungBlockIdentification :
    S05_Lem5_12_DegreeOneYoungBlockIdentificationStatement := by
  intro n action
  exact U1_eq_concreteDegreeOneYoungBlockSum action

/-- Faithful degree-one equality for a fixed family of concrete Young actions. -/
theorem S05_Lem5_12_U1_eq_concreteDegreeOneYoungBlockSum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action :=
  S05_Lem5_12_degreeOneYoungBlockIdentification action

/-- The Young blocks outside `U_1`, represented in row-language. -/
abbrev S05_Lem5_12_nonU1YoungBlocks (n : Nat) : Finset (YoungDiagram n) :=
  nonU1YoungBlocks n

/-- Membership in the complement of the two `U_1` Young blocks. -/
theorem S05_Lem5_12_mem_nonU1YoungBlocks_iff {n : Nat} (lam : YoungDiagram n) :
    lam ∈ S05_Lem5_12_nonU1YoungBlocks n ↔
      ¬ IsOneRow lam ∧ ¬ IsStandard lam := by
  simp [S05_Lem5_12_nonU1YoungBlocks, nonU1YoungBlocks]

end DictatorshipTesting
