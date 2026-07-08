import DictatorshipTesting.Paper.Aux_StandardYoungTableaux

/-
Direct reverse imports (generated):
- `DictatorshipTesting.Paper.AppA_ThmA_03_RegularYoungBlockDecomposition`
- `DictatorshipTesting.PaperAux`
- `DictatorshipTesting.PaperPlaceholders`
-/

/-!
Paper statement: Lemma A.5 (`lem:app-tableau-swap-connected`)
Title in paper: Connectedness of standard tableaux.

Status: external: ingredient bundled into Theorem A.3.  The current Lean
development contains local adjacent-swap constructions for standard tableaux,
but it consumes the global connectedness theorem only through the packaged
spectral-block model axioms in
`AppA_ThmA_03_RegularYoungBlockDecomposition`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Marker proposition for the not-yet-formalized Lemma A.5.  It stands for
global connectedness of standard tableaux under adjacent swaps, used by the
packaged spectral-block model input in Theorem A.3. -/
inductive AppA_LemA_05_StandardTableauxSwapConnectednessStatement : Prop

/-- External input Lemma A.5: connectedness of standard tableaux. -/
axiom AppA_LemA_05_standardTableauxSwapConnectedness :
    AppA_LemA_05_StandardTableauxSwapConnectednessStatement

end DictatorshipTesting
