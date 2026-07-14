/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_13_MatchingSubgroupEigenbasis`
-/
import DictatorshipTesting.Paper.Defs.S05_Def5_07a_TwoBoxRemovals
import DictatorshipTesting.Paper.S05_Lem5_10_SignedTwoBoxOrthogonalBranching

/-!
Paper statement: Definition 5.8 `def:signed-two-box-extension-spaces`
Title in paper: Signed two-box extension spaces.

The coordinate constructions are defined here and consumed by the later
recursive matching-eigenbasis proof.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

local instance S05_Def5_08_adjacentSameRowDecidable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameRow T a) :=
  Classical.propDecidable _

local instance S05_Def5_08_adjacentSameColDecidable
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    Decidable (adjacentSameCol T a) :=
  Classical.propDecidable _

/-- Extend tableau coordinates from one ordered two-box child fiber to the
parent tableau space, with zero coordinates off that fiber. -/
noncomputable def S05_twoStepExtensionEmbedding
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    TableauSpace (deleteTwoRemovableRowsDiagram lam p) -> TableauSpace lam :=
  fun f T =>
    ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
      f U * tableauBasisVec (S05_Lem5_10_twoBoxExtensionTableau lam p U) T


/-- The sign attached to an ordered two-step removal.  Under the existing
equivalence with `TaggedTwoStripChildrenSized`, weakly increasing deletion rows
are the positive/horizontal summand and decreasing rows are the
negative/vertical summand. -/
def S05_signedTwoBoxRemovalSign
    {n : Nat} {lam : YoungDiagram ((n + 1) + 1)}
    (p : TwoStepRemovableRows lam) : Real :=
  if p.first.1 <= p.second.1 then 1 else -1

/-- The diagonal coefficient of the final adjacent block, written directly
from the two fixed deleted corners. -/
noncomputable def S05_twoBoxFinalDiagCoeff
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) : Real :=
  ((YoungCell.content (firstDeletedCornerOfTwoStep lam p) -
    YoungCell.content (secondDeletedCornerOfTwoStepInParent lam p) : Int) :
      Real)⁻¹


/-- A positive/horizontal ordered removal cannot put the final labels in one
column. -/
theorem S05_twoBoxExtension_not_sameCol_of_positive
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (hpos : p.first.1 <= p.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    ¬ adjacentSameCol (S05_Lem5_10_twoBoxExtensionTableau lam p U)
      (Fin.last n) := by
  intro hcol
  have hlt := adjacent_row_lt_of_sameCol
    (S05_Lem5_10_twoBoxExtensionTableau lam p U) (Fin.last n) hcol
  rw [S05_Lem5_10_twoBoxExtensionTableau_final_loCell_row,
    S05_Lem5_10_twoBoxExtensionTableau_final_hiCell_row] at hlt
  omega

/-- A negative/vertical ordered removal has distinct deletion rows, so its
final labels cannot lie in one row. -/
theorem S05_twoBoxExtension_not_sameRow_of_negative
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (hneg : ¬ p.first.1 <= p.second.1)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    ¬ adjacentSameRow (S05_Lem5_10_twoBoxExtensionTableau lam p U)
      (Fin.last n) := by
  rw [S05_Lem5_10_twoBoxExtensionTableau_final_sameRow_iff]
  omega


/-- The normalized `+1` eigenvector in a swappable Young two-by-two block. -/
noncomputable def S05_normalizedAdjacentPlusVector
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (_hrow : ¬ adjacentSameRow T a) (_hcol : ¬ adjacentSameCol T a) :
    TableauSpace lam :=
  let d := youngAdjacentDiagCoeff T a
  fun S => (Real.sqrt (2 * (1 + d)))⁻¹ *
    (tableauBasisVec T S +
      youngAdjacentOperator a (tableauBasisVec T) S)

/-- The normalized `-1` eigenvector in a swappable Young two-by-two block. -/
noncomputable def S05_normalizedAdjacentMinusVector
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n)
    (_hrow : ¬ adjacentSameRow T a) (_hcol : ¬ adjacentSameCol T a) :
    TableauSpace lam :=
  let d := youngAdjacentDiagCoeff T a
  fun S => (Real.sqrt (2 * (1 - d)))⁻¹ *
    (tableauBasisVec T S -
      youngAdjacentOperator a (tableauBasisVec T) S)


/-- The signed unit vector associated to one child basis tableau. -/
noncomputable def S05_signedTwoBoxExtensionBasisVector
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam)
    (U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)) :
    TableauSpace lam :=
  let T := S05_Lem5_10_twoBoxExtensionTableau lam p U
  let a := Fin.last n
  if hpos : p.first.1 <= p.second.1 then
    if hrow : adjacentSameRow T a then
      tableauBasisVec T
    else
      S05_normalizedAdjacentPlusVector T a hrow
        (S05_twoBoxExtension_not_sameCol_of_positive lam p hpos U)
  else
    have hrow := S05_twoBoxExtension_not_sameRow_of_negative lam p hpos U
    if hcol : adjacentSameCol T a then
      tableauBasisVec T
    else
      S05_normalizedAdjacentMinusVector T a hrow hcol


/-- The explicit coordinate embedding associated to one signed two-box child.
Its basis images are the signed extension vectors above. -/
noncomputable def S05_signedTwoBoxChildEmbedding
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1))
    (p : TwoStepRemovableRows lam) :
    TableauSpace (deleteTwoRemovableRowsDiagram lam p) -> TableauSpace lam :=
  fun f T =>
    ∑ U : StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p),
      f U * S05_signedTwoBoxExtensionBasisVector lam p U T


/-- The global finite index of signed-child tableau basis vectors. -/
abbrev S05_SignedTwoBoxBasisIndex
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :=
  Sigma fun p : TwoStepRemovableRows lam =>
    StandardYoungTableau (deleteTwoRemovableRowsDiagram lam p)


noncomputable def S05_Def5_08_signedTwoBoxExtensionBasisVector :=
  @S05_signedTwoBoxExtensionBasisVector

noncomputable def S05_Def5_08_signedTwoBoxChildEmbedding :=
  @S05_signedTwoBoxChildEmbedding

abbrev S05_Def5_08_SignedTwoBoxBasisIndex
    {n : Nat} (lam : YoungDiagram ((n + 1) + 1)) :=
  S05_SignedTwoBoxBasisIndex lam

end DictatorshipTesting
