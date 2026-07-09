import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.Aux_TableauDimension
import DictatorshipTesting.Paper.S05_Def5_07_YoungBlockEnergyProfile
import DictatorshipTesting.Paper.S05_Def5_08_U1CompatibleYoungBlockProfile
import DictatorshipTesting.Paper.Aux_Def_TableauEvenHeight
import DictatorshipTesting.Paper.Aux_Def_TableauOddHeight
import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization
import DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum
import DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification
import DictatorshipTesting.Paper.AppA_LemA_04_StandardTableauxSwapConnectedness

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenSpectralBridge`
- `DictatorshipTesting.Paper.S05_Lem5_20_OddSpectralBridge`
-/


/-!
Paper statement: Lemma 5.18 (`lem:regular-young-block-decomposition`)
Title in paper: Regular Young-block decomposition.

Status: internal assembly from external Appendix A ingredients.  A.1, A.2,
A.3, and A.4 are the named representation-theoretic inputs; this file contains
the theorem that assembles them into the dimension-parameterized
spectral-block model consumed by the active Theorem 4.10 path.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.18 model projection: each Young-block energy is nonnegative. -/
theorem S05_Lem5_18_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Lemma 5.18 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem S05_Lem5_18_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

/-- Lemma 5.18 assembly theorem for the tableau-count even route, from the
explicit classical Appendix A ingredients.

This theorem contains no representation-theoretic axiom of its own; it only
assembles the precise A.1/A.2/A.3/A.4 component inputs into the compact
`SpectralBlockModelInputWithDim` interface consumed by Section 5. -/
theorem spectralBlockModelInputWithDim_even_from_appA_inputs
    (hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (hA3 : AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement)
    (hA4 : AppA_LemA_04_StandardTableauxSwapConnectednessStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) := by
  intro F
  rcases hA1 F with ⟨energyData⟩
  rcases hA2.1 m hm energyData with ⟨traceData⟩
  let energy : YoungBlockEnergyModel F :=
    { blockEnergy := energyData.blockEnergy
      nonneg := energyData.nonneg
      u1_identification := hA3 energyData }
  let scalar :
      MatchingAverageScalarModelWithDim
        (fun lam : YoungDiagram (2 * m) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)
        F energy.blockEnergy :=
    { theta := traceData.theta
      scalarity := hA4 traceData
      trace_value := traceData.trace_value }
  exact ⟨energy, ⟨scalar⟩⟩

/-- Appendix A spectral-block model input for the tableau-count even route. -/
theorem spectralBlockModelInputWithDim_even_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) :=
  spectralBlockModelInputWithDim_even_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_03_degreeOneYoungBlockIdentification
    AppA_LemA_04_standardTableauxSwapConnectedness
    m hm

/-- Lemma 5.18 assembly theorem for the tableau-count odd route, from the
explicit classical Appendix A ingredients.

This is the odd analogue of
`spectralBlockModelInputWithDim_even_from_appendixA`, with block dimension
`tableauDim` and height `hOddTableau`. -/
theorem spectralBlockModelInputWithDim_odd_from_appA_inputs
    (hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (hA3 : AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement)
    (hA4 : AppA_LemA_04_StandardTableauxSwapConnectednessStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) := by
  intro F
  rcases hA1 F with ⟨energyData⟩
  rcases hA2.2 m hm energyData with ⟨traceData⟩
  let energy : YoungBlockEnergyModel F :=
    { blockEnergy := energyData.blockEnergy
      nonneg := energyData.nonneg
      u1_identification := hA3 energyData }
  let scalar :
      MatchingAverageScalarModelWithDim
        (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
        F energy.blockEnergy :=
    { theta := traceData.theta
      scalarity := hA4 traceData
      trace_value := traceData.trace_value }
  exact ⟨energy, ⟨scalar⟩⟩

/-- Appendix A spectral-block model input for the tableau-count odd route. -/
theorem spectralBlockModelInputWithDim_odd_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) :=
  spectralBlockModelInputWithDim_odd_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_03_degreeOneYoungBlockIdentification
    AppA_LemA_04_standardTableauxSwapConnectedness
    m hm

end DictatorshipTesting
