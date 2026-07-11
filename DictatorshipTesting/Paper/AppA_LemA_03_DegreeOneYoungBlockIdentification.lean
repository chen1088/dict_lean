import DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_19_RegularYoungBlockDecomposition`
-/


/-!
Paper statement: Lemma A.3 (`lem:app-u1-young-blocks`)
Title in paper: Degree-one Young-block identification.

Status: external: Appendix A representation-theoretic input.  The axiom below
states the faithful equality between `U1` and the concrete one-row plus
standard matrix-coefficient blocks.  The numerical distance identity is
derived later from this equality and the internal orthogonal decomposition.
-/

noncomputable section

namespace DictatorshipTesting

/-- Faithful Lemma A.3 statement: for every supplied Young orthogonal action,
`U_1` is exactly the concrete sum of the one-row and standard `(n-1,1)`
matrix-coefficient blocks. -/
def AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement : Prop :=
  ∀ {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam),
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action

/-- External input Lemma A.3: degree-one Young-block identification. -/
axiom AppA_LemA_03_degreeOneYoungBlockIdentification :
    AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement

/-- Faithful A.3 equality for a fixed family of concrete Young actions. -/
theorem AppA_LemA_03_U1_eq_concreteDegreeOneYoungBlockSum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action :=
  AppA_LemA_03_degreeOneYoungBlockIdentification action

/-- The Young blocks outside `U_1`, represented in row-language. -/
abbrev AppA_LemA_03_nonU1YoungBlocks (n : Nat) : Finset (YoungDiagram n) :=
  nonU1YoungBlocks n

/-- Membership in the complement of the two `U_1` Young blocks. -/
theorem AppA_LemA_03_mem_nonU1YoungBlocks_iff {n : Nat} (lam : YoungDiagram n) :
    lam ∈ AppA_LemA_03_nonU1YoungBlocks n ↔
      ¬ IsOneRow lam ∧ ¬ IsStandard lam := by
  simp [AppA_LemA_03_nonU1YoungBlocks, nonU1YoungBlocks]

end DictatorshipTesting
