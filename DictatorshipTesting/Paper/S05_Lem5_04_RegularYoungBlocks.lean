import DictatorshipTesting.Paper.S05_Def5_03_YoungBlock

/-!
Paper statement: Lemma 5.4 (`lem:regular-young-blocks`)
Title in paper: Regular Young blocks.

Status: paper-facing owner file for the rewritten Section 5 statement.  The
regular-representation decomposition into Young blocks is currently part of the
external spectral-block model interface, not an internal Lean proof.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.4 interface: nonnegative block-energy decomposition.  This aliases
the existing numerical input, rather than proving the representation theorem. -/
abbrev S05_Lem5_04_YoungBlockDecompositionInput {n : Nat}
    (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  YoungBlockDecompositionInput blockEnergy

/-- Lemma 5.4 interface: `U_1` is represented by the one-row and standard Young
blocks in the numerical model. -/
abbrev S05_Lem5_04_U1YoungBlockIdentificationInput {n : Nat}
    (F : Perm (Fin n) → ℝ) (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  U1YoungBlockIdentificationInput F blockEnergy

/-- Lemma 5.4 model projection: each Young-block energy is nonnegative. -/
theorem S05_Lem5_04_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : S05_Def5_03_YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Lemma 5.4 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem S05_Lem5_04_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : S05_Def5_03_YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

end DictatorshipTesting
