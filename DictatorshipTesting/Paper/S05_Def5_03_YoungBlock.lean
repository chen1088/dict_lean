import DictatorshipTesting.Paper.Aux_SpectralBridgeRepresentationInputs

/-!
Paper statement: Definition 5.3
Title in paper: Young block.

Status: the current Lean scaffold represents Young-block indices by
`YoungDiagram n` and packages the analytic block decomposition through the
interfaces in `Aux_SpectralBridgeRepresentationInputs`.
-/

noncomputable section

namespace DictatorshipTesting

/-- Current Lean shadow of a Young block index. -/
abbrev S05_YoungBlock (n : Nat) := YoungDiagram n

end DictatorshipTesting
