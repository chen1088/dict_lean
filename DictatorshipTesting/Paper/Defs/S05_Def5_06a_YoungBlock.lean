import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs

/-
Direct reverse imports:
- `DictatorshipTesting`
-/


/-!
Paper statement: Definition 5.6 part (a) `def:young-block`
Title in paper: Young matrix coefficients, blocks, and energies.

Status: definition/interface. The current Lean scaffold represents Young-block indices by
`YoungDiagram n`. The later numerical interfaces for block energies and
`U_1` identification have their own paper-facing definition files.
-/

noncomputable section

namespace DictatorshipTesting

/-- Current Lean shadow of a Young block index. -/
abbrev S05_YoungBlock (n : Nat) := YoungDiagram n

end DictatorshipTesting
