import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Aux_TableauDimension
import DictatorshipTesting.Paper.S05_Lem5_37_EvenCertificate
import DictatorshipTesting.Paper.S05_Lem5_39_OddCertificate
import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization
import DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum
import DictatorshipTesting.Paper.AppA_LemA_04_DegreeOneYoungBlockIdentification
import DictatorshipTesting.Paper.AppA_LemA_05_StandardTableauxSwapConnectedness

/-!
Paper statement: Theorem A.3 (`thm:app-regular-young-decomposition`)
Title in paper: Regular Young-block decomposition.

Status: external: Appendix A representation-theoretic input.  This is the
actual Lean boundary consumed by the active Theorem 4.10 path: Appendix A
packages the classical Specht/Young-orthogonal representation theory into the
dimension-parameterized spectral-block model inputs below.
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
    (energy : YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Theorem A.3 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem AppA_ThmA_03_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

/-- Packaged Appendix A spectral-block model input for the tableau-count even
route, from the explicit classical Appendix A ingredients.

This packages the classical representation-theoretic ingredients used in the
paper: regular Specht-block decomposition, `U_1` identification, matching
average scalarity, and the local trace/scalar formula with block dimension
`tableauDim` and height `hEvenTableau`. -/
axiom spectralBlockModelInputWithDim_even_from_appA_inputs
    (_hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (_hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (_hA4 : AppA_LemA_04_DegreeOneYoungBlockIdentificationStatement)
    (_hA5 : AppA_LemA_05_StandardTableauxSwapConnectednessStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)

/-- Appendix A spectral-block model input for the tableau-count even route. -/
theorem spectralBlockModelInputWithDim_even_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) :=
  spectralBlockModelInputWithDim_even_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_04_degreeOneYoungBlockIdentification
    AppA_LemA_05_standardTableauxSwapConnectedness
    m hm

/-- Packaged Appendix A spectral-block model input for the tableau-count odd
route, from the explicit classical Appendix A ingredients.

This is the odd analogue of
`spectralBlockModelInputWithDim_even_from_appendixA`, with block dimension
`tableauDim` and height `hOddTableau`. -/
axiom spectralBlockModelInputWithDim_odd_from_appA_inputs
    (_hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (_hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (_hA4 : AppA_LemA_04_DegreeOneYoungBlockIdentificationStatement)
    (_hA5 : AppA_LemA_05_StandardTableauxSwapConnectednessStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)

/-- Appendix A spectral-block model input for the tableau-count odd route. -/
theorem spectralBlockModelInputWithDim_odd_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) :=
  spectralBlockModelInputWithDim_odd_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_04_degreeOneYoungBlockIdentification
    AppA_LemA_05_standardTableauxSwapConnectedness
    m hm

end DictatorshipTesting
