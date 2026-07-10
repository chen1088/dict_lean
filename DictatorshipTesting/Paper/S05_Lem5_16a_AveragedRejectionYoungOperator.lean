import DictatorshipTesting.Paper.S05_Lem5_15_YoungBasisScalarCommutant

/-
Direct reverse imports:
- `DictatorshipTesting`
-/

/-!
Preparatory interface below Lemma 5.16.

This file names the missing operator-level object needed to turn the generic
Young-basis scalar commutant theorem into the matching-average scalarity
bridge.  It does not assert scalarity and does not construct the group-algebra
operator `rho_lambda(q)`.  Instead, it records the precise data still needed
for one tableau-coordinate Young block.
-/

noncomputable section

namespace DictatorshipTesting

/-- Operator-level data for the averaged matching rejection on one
tableau-coordinate Young block.

Mathematically, this is the data one would get from the operator
`rho_lambda(q)`, where `q` is the averaged high matching idempotent.  The fields
only assert linearity and commutation with the explicit operators already
formalized in Lean; scalarity is proved from these fields by Lemma 5.15. -/
structure AveragedRejectionYoungOperatorData {n : Nat}
    (lam : YoungDiagram (n + 1)) where
  operator : TableauSpace lam -> TableauSpace lam
  map_add :
    forall f g : TableauSpace lam,
      operator (fun T => f T + g T) = fun T => operator f T + operator g T
  map_smul :
    forall (c : Real) (f : TableauSpace lam),
      operator (fun T => c * f T) = fun T => c * operator f T
  commutes_adjacent :
    forall (a : Fin n) (f : TableauSpace lam),
      operator (youngAdjacentOperator a f) =
        youngAdjacentOperator a (operator f)
  commutes_content :
    forall (a : Fin (n + 1)) (f : TableauSpace lam),
      operator (jucysMurphyDiagonalOperator a f) =
        jucysMurphyDiagonalOperator a (operator f)

/-- The averaged-rejection operator data gives exactly the commutation package
needed by the generic Young-basis scalar commutant theorem. -/
def AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (data : AveragedRejectionYoungOperatorData lam) :
    YoungModelOperatorCommutationData lam where
  op := data.operator
  map_add := data.map_add
  map_smul := data.map_smul
  commutes_adjacent := data.commutes_adjacent
  commutes_content := data.commutes_content

/-- Adjacent-operator commutation extracted from the averaged-rejection
operator interface. -/
theorem averagedRejectionYoungOperator_commutes_adjacent
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (data : AveragedRejectionYoungOperatorData lam)
    (a : Fin n) (f : TableauSpace lam) :
    data.operator (youngAdjacentOperator a f) =
      youngAdjacentOperator a (data.operator f) := by
  exact data.commutes_adjacent a f

/-- Diagonal-content commutation extracted from the averaged-rejection operator
interface. -/
theorem averagedRejectionYoungOperator_commutes_content
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (data : AveragedRejectionYoungOperatorData lam)
    (a : Fin (n + 1)) (f : TableauSpace lam) :
    data.operator (jucysMurphyDiagonalOperator a f) =
      jucysMurphyDiagonalOperator a (data.operator f) := by
  exact data.commutes_content a f

/-- The averaged-rejection operator interface instantiates the generic
commutant-to-scalar theorem from Lemma 5.15.  This is a one-block statement; it
does not yet produce the global `MatchingAverageScalarityInput`. -/
theorem averagedRejectionYoungOperator_scalar_on_basis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (hconn : External.AppendixA.StandardTableauxSwapConnectedStatement)
    (data : AveragedRejectionYoungOperatorData lam)
    (T0 T : StandardYoungTableau lam) :
    data.operator (tableauBasisVec T) =
      fun U =>
        data.toYoungModelOperatorCommutationData.basisScalar T0 *
          tableauBasisVec T U := by
  exact S05_Lem5_15_youngModelOperator_scalar_on_basis
    hconn data.toYoungModelOperatorCommutationData T0 T

end DictatorshipTesting
