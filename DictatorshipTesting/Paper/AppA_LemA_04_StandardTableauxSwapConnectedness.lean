import DictatorshipTesting.External.AppendixA.A04_TableauxSwapConnectedness

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_16_BlockScalarOfTheAveragedRejection`
- `DictatorshipTesting.Paper.S05_Lem5_18_RegularYoungBlockDecomposition`
-/


/-!
Paper statement: Lemma A.4 (`lem:app-tableau-swap-connected`)
Title in paper: Connectedness of standard tableaux.

Status: proven internally.  The proof identifies standard tableaux with linear
extensions of the Young poset and connects linear extensions by adjacent swaps
of incomparable elements.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma A.4 interface: connectedness of the standard-tableau adjacent-swap
graph for each fixed Young diagram. -/
def AppA_LemA_04_StandardTableauxSwapConnectednessStatement : Prop :=
  External.AppendixA.StandardTableauxSwapConnectedStatement

/-- Lemma A.4: connectedness of standard tableaux. -/
theorem AppA_LemA_04_standardTableauxSwapConnectedness :
    AppA_LemA_04_StandardTableauxSwapConnectednessStatement :=
  External.AppendixA.standardTableauxSwapConnected

end DictatorshipTesting
