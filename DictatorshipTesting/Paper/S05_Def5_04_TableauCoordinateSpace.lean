import DictatorshipTesting.Paper.Aux_TableauDimension
import DictatorshipTesting.Paper.Aux_YoungOrthogonal

/-!
Paper statement: Definition 5.4 (`def:tableau-coordinate-space`)
Title in paper: Tableau coordinate space.

Status: paper-facing wrapper for the tableau-count dimension and coordinate
space used by the Young-basis operator model.
-/

noncomputable section

namespace DictatorshipTesting

/-- Definition 5.4 wrapper: tableau-count dimension. -/
abbrev S05_Def5_04_tableauDim {n : Nat} (lam : YoungDiagram n) : ℝ :=
  tableauDim lam

/-- Definition 5.4 wrapper: coordinate space with basis indexed by tableaux. -/
abbrev S05_Def5_04_TableauSpace {n : Nat} (lam : YoungDiagram n) :=
  TableauSpace lam

/-- Definition 5.4 wrapper: coordinate basis vector. -/
abbrev S05_Def5_04_tableauBasisVec {n : Nat} {lam : YoungDiagram n}
    (T : StandardYoungTableau lam) :=
  tableauBasisVec T

end DictatorshipTesting
