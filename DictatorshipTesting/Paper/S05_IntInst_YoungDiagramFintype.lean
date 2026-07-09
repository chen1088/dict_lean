import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungDiagram

/-!
Definition file for `youngDiagramFintype`.

This file contains one primary reusable declaration split out of
`DictatorshipTesting.Paper.Defs`.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

noncomputable instance youngDiagramFintype (n : ℕ) : Fintype (YoungDiagram n) := by
  classical
  exact Fintype.ofInjective YoungDiagram.row (by
    intro lam mu h
    cases lam
    cases mu
    simp at h
    simp [h])

end DictatorshipTesting
