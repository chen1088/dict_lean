import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_18_RegularYoungBlockDecomposition`
-/


/-!
Paper statement: Lemma A.3 (`lem:app-u1-young-blocks`)
Title in paper: Degree-one Young-block identification.

Status: external: Appendix A representation-theoretic input.  The current Lean
scaffold records this identification as the interface
`U1YoungBlockIdentificationInput` inside the spectral-block model.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma A.3 interface: the Young-block energy data from Theorem A.1 identifies
the distance to `U_1` as the sum of all non-`U_1` block energies. -/
def AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement : Prop :=
  ∀ {n : Nat} {F : Perm (Fin n) -> ℝ}
    (energy : AppA_YoungBlockEnergyData F),
    U1YoungBlockIdentificationInput F energy.blockEnergy

/-- External input Lemma A.3: degree-one Young-block identification. -/
axiom AppA_LemA_03_degreeOneYoungBlockIdentification :
    AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement

/-- Current Lean interface for the `U_1` Young-block identification. -/
abbrev AppA_LemA_03_U1YoungBlockIdentification {n : Nat}
    (F : Perm (Fin n) -> ℝ) (blockEnergy : YoungDiagram n -> ℝ) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

/-- The Young blocks outside `U_1`, represented in row-language. -/
abbrev AppA_LemA_03_nonU1YoungBlocks (n : Nat) : Finset (YoungDiagram n) :=
  nonU1YoungBlocks n

/-- Membership in the complement of the two `U_1` Young blocks. -/
theorem AppA_LemA_03_mem_nonU1YoungBlocks_iff {n : Nat} (lam : YoungDiagram n) :
    lam ∈ AppA_LemA_03_nonU1YoungBlocks n ↔
      ¬ IsOneRow lam ∧ ¬ IsStandard lam := by
  simp [AppA_LemA_03_nonU1YoungBlocks, nonU1YoungBlocks]

/-- Lemma A.3 interface projection: the distance to `U_1` is the sum of the
block energies outside the one-row and standard blocks. -/
theorem AppA_LemA_03_l2DistSqToU1_eq_nonU1_sum {n : Nat}
    {F : Perm (Fin n) -> ℝ} {blockEnergy : YoungDiagram n -> ℝ}
    (h : AppA_LemA_03_U1YoungBlockIdentification F blockEnergy) :
    l2DistSqToU1 F =
      (AppA_LemA_03_nonU1YoungBlocks n).sum blockEnergy := by
  exact h

end DictatorshipTesting
