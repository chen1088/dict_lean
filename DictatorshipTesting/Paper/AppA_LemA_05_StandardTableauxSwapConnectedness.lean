import DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum
import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.AppA_ThmA_03_RegularYoungBlockDecomposition`
-/

/-!
Paper statement: Lemma A.5 (`lem:app-tableau-swap-connected`)
Title in paper: Connectedness of standard tableaux.

Status: external: ingredient bundled into Theorem A.3.  The current Lean
development contains local adjacent-swap constructions for standard tableaux,
but it consumes the global connectedness theorem only through the A.3
spectral-block assembly theorem in
`AppA_ThmA_03_RegularYoungBlockDecomposition`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma A.5 interface: standard-tableau connectedness supplies scalarity of
the matching average for the trace/scalar data from Theorem A.2. -/
def AppA_LemA_05_StandardTableauxSwapConnectednessStatement : Prop :=
  ∀ {n : Nat} {dim height : YoungDiagram n -> ℝ}
    {F : Perm (Fin n) -> ℝ}
    {energy : AppA_YoungBlockEnergyData F}
    (traceData : AppA_TraceScalarDataWithDim dim height energy),
    MatchingAverageScalarityInput F energy.blockEnergy traceData.theta

/-- External input Lemma A.5: connectedness of standard tableaux. -/
axiom AppA_LemA_05_standardTableauxSwapConnectedness :
    AppA_LemA_05_StandardTableauxSwapConnectednessStatement

end DictatorshipTesting
