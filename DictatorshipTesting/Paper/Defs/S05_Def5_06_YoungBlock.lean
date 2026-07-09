import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- none
-/


/-!
Paper statement: Definition 5.6 (`def:young-block`)
Title in paper: Young block.

Status: definition/interface. The current Lean scaffold represents Young-block indices by
`YoungDiagram n`. The later numerical interfaces for block energies and
`U_1` identification have their own paper-facing definition files.
-/

noncomputable section

namespace DictatorshipTesting

/-- Current Lean shadow of a Young block index. -/
abbrev S05_YoungBlock (n : Nat) := YoungDiagram n

end DictatorshipTesting
