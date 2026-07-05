import DictatorshipTesting.Paper.S05_Def5_03_YoungBlock

/-!
Paper statement: Theorem A.3 (`thm:app-regular-young-decomposition`)
Title in paper: Regular Young-block decomposition.

Status: Appendix A external representation-theoretic input.  The
regular-representation decomposition into Young blocks is currently represented
by the external spectral-block model interface, not an internal Lean proof.
-/

noncomputable section

namespace DictatorshipTesting

/-- Theorem A.3 interface: nonnegative block-energy decomposition.  This aliases
the existing numerical input, rather than proving the representation theorem. -/
abbrev AppA_ThmA_03_YoungBlockDecompositionInput {n : Nat}
    (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  YoungBlockDecompositionInput blockEnergy

/-- Theorem A.3 interface: `U_1` is represented by the one-row and standard Young
blocks in the numerical model. -/
abbrev AppA_ThmA_03_U1YoungBlockIdentificationInput {n : Nat}
    (F : Perm (Fin n) → ℝ) (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

/-- Theorem A.3 model projection: each Young-block energy is nonnegative. -/
theorem AppA_ThmA_03_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : S05_Def5_03_YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Theorem A.3 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem AppA_ThmA_03_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : S05_Def5_03_YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

end DictatorshipTesting
