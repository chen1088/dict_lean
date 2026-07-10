import DictatorshipTesting.External.AppendixA.A04_TableauxSwapConnectedness

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_18_RegularYoungBlockDecomposition`
-/


/-!
Paper statement: Lemma A.4 (`lem:app-tableau-swap-connected`)
Title in paper: Connectedness of standard tableaux.

Status: external: connectedness of the standard-tableau adjacent-swap graph.
The current Lean development contains local adjacent-swap constructions and an
abstract finite-list preservation layer, but the global connectedness theorem is
still an Appendix A input.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma A.4 interface: connectedness of the standard-tableau adjacent-swap
graph for each fixed Young diagram. -/
def AppA_LemA_04_StandardTableauxSwapConnectednessStatement : Prop :=
  External.AppendixA.StandardTableauxSwapConnectedStatement

/-- External input Lemma A.4: connectedness of standard tableaux. -/
axiom AppA_LemA_04_standardTableauxSwapConnectedness :
    AppA_LemA_04_StandardTableauxSwapConnectednessStatement

end DictatorshipTesting
