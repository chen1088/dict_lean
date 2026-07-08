import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_03_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Lemma A.4 (`lem:app-u1-young-blocks`)
Title in paper: Degree-one Young-block identification.

Status: external: Appendix A representation-theoretic input.  The current Lean
scaffold records this identification as the interface
`U1YoungBlockIdentificationInput` inside the spectral-block model.
-/

noncomputable section

namespace DictatorshipTesting

/-- Marker proposition for the not-yet-formalized Lemma A.4.  It stands for
the representation-theoretic identification of `U_1` with the degree-one Young
blocks, used by the packaged spectral-block model input in Theorem A.3. -/
inductive AppA_LemA_04_DegreeOneYoungBlockIdentificationStatement : Prop

/-- External input Lemma A.4: degree-one Young-block identification. -/
axiom AppA_LemA_04_degreeOneYoungBlockIdentification :
    AppA_LemA_04_DegreeOneYoungBlockIdentificationStatement

/-- Current Lean interface for the `U_1` Young-block identification. -/
abbrev AppA_LemA_04_U1YoungBlockIdentification {n : Nat}
    (F : Perm (Fin n) -> ℝ) (blockEnergy : YoungDiagram n -> ℝ) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

/-- The Young blocks outside `U_1`, represented in row-language. -/
abbrev AppA_LemA_04_nonU1YoungBlocks (n : Nat) : Finset (YoungDiagram n) :=
  nonU1YoungBlocks n

/-- Membership in the complement of the two `U_1` Young blocks. -/
theorem AppA_LemA_04_mem_nonU1YoungBlocks_iff {n : Nat} (lam : YoungDiagram n) :
    lam ∈ AppA_LemA_04_nonU1YoungBlocks n ↔
      ¬ IsOneRow lam ∧ ¬ IsStandard lam := by
  simp [AppA_LemA_04_nonU1YoungBlocks, nonU1YoungBlocks]

/-- Lemma A.4 interface projection: the distance to `U_1` is the sum of the
block energies outside the one-row and standard blocks. -/
theorem AppA_LemA_04_l2DistSqToU1_eq_nonU1_sum {n : Nat}
    {F : Perm (Fin n) -> ℝ} {blockEnergy : YoungDiagram n -> ℝ}
    (h : AppA_LemA_04_U1YoungBlockIdentification F blockEnergy) :
    l2DistSqToU1 F =
      (AppA_LemA_04_nonU1YoungBlocks n).sum blockEnergy := by
  exact h

end DictatorshipTesting
