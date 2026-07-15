import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import AlgebraicLibrary.Young.TableauDimension
import AlgebraicLibrary.Young.TableauSumOfSquares
import DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks
import AlgebraicLibrary.Young.TableauTrace
import Mathlib.LinearAlgebra.Basis.Basic
import DictatorshipTesting.Paper.S05_Thm5_02_YoungOrthogonalAction
import DictatorshipTesting.Paper.S05_Thm5_03_JucysMurphyContentAction
import DictatorshipTesting.Paper.S05_Lem5_04_ContentSeparationAndTableauConnectivity
import DictatorshipTesting.Paper.S05_Lem5_05_YoungBasisScalarCommutant

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S04_Thm4_04_MatchingGap`
- `DictatorshipTesting.Paper.S05_Lem5_06_YoungMatrixCoefficientOrthogonality`
- `DictatorshipTesting.Paper.S05_Lem5_08_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
/-!

Internal regular-representation machinery for Lemmas 5.9--5.11. This file
proves matrix-coefficient orthogonality and constructs the concrete Young-block
decomposition. The later `U1` and matching-weighted arguments live in their
numbered Lemma 5.9 and Proposition 5.16 modules, so this implementation module has
no forward dependency on them.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

local instance standardYoungTableauDecidableEqForRegularBlocks
    {n : Nat} {lam : YoungDiagram n} :
    DecidableEq (StandardYoungTableau lam) :=
  Classical.decEq _

/-- The coordinate rank-one operator `|T><V|` on one tableau space. -/
def tableauRankOne {n : Nat} {lam : YoungDiagram n}
    (T V : StandardYoungTableau lam) :
    TableauSpace lam → TableauSpace lam :=
  fun f U => f V * tableauBasisVec T U

/-- Conjugate a coordinate rank-one operator by one represented
permutation. -/
def youngConjugatedRankOne {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (g : Perm (Fin (n + 1))) :
    TableauSpace lam → TableauSpace lam :=
  fun f =>
    action.rep.rho g
      (tableauRankOne T V (action.rep.rho g.symm f))

/-- Uniform conjugation average of a coordinate rank-one operator. -/
def youngAveragedRankOne {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam) :
    TableauSpace lam → TableauSpace lam :=
  fun f =>
    (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ •
      ∑ g : Perm (Fin (n + 1)), youngConjugatedRankOne action T V g f

/-- Orthogonality of the represented permutation moves an inverse action from
one side of a basis matrix coefficient to the other. -/
theorem rho_symm_basis_coordinate
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (g : Perm (Fin (n + 1)))
    (U V : StandardYoungTableau lam) :
    action.rep.rho g.symm (tableauBasisVec U) V =
      action.rep.rho g (tableauBasisVec V) U := by
  calc
    action.rep.rho g.symm (tableauBasisVec U) V =
        tableauInner (tableauBasisVec V)
          (action.rep.rho g.symm (tableauBasisVec U)) := by
      rw [tableauInner_left_basis]
    _ = tableauInner
          (action.rep.rho g (tableauBasisVec V))
          (action.rep.rho g
            (action.rep.rho g.symm (tableauBasisVec U))) := by
      rw [action.rho_inner]
    _ = tableauInner
          (action.rep.rho g (tableauBasisVec V))
          (tableauBasisVec U) := by
      rw [action.rho_rightInverse]
    _ = action.rep.rho g (tableauBasisVec V) U := by
      rw [tableauInner_right_basis]

/-- Conjugating a rank-one operator preserves its trace. -/
theorem youngConjugatedRankOne_trace
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (g : Perm (Fin (n + 1))) :
    tableauOperatorTrace (youngConjugatedRankOne action T V g) =
      if T = V then 1 else 0 := by
  classical
  unfold tableauOperatorTrace youngConjugatedRankOne tableauRankOne
  calc
    (∑ U : StandardYoungTableau lam,
      action.rep.rho g
        (fun W =>
          action.rep.rho g.symm (tableauBasisVec U) V *
            tableauBasisVec T W) U) =
        ∑ U : StandardYoungTableau lam,
          action.rep.rho g.symm (tableauBasisVec U) V *
            action.rep.rho g (tableauBasisVec T) U := by
      apply Finset.sum_congr rfl
      intro U _hU
      change action.rep.rho g
          (action.rep.rho g.symm (tableauBasisVec U) V •
            tableauBasisVec T) U = _
      rw [action.rep.map_smul]
      rfl
    _ = ∑ U : StandardYoungTableau lam,
        action.rep.rho g (tableauBasisVec V) U *
          action.rep.rho g (tableauBasisVec T) U := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [rho_symm_basis_coordinate]
    _ = tableauInner
        (action.rep.rho g (tableauBasisVec V))
        (action.rep.rho g (tableauBasisVec T)) := by
      rfl
    _ = tableauInner (tableauBasisVec V) (tableauBasisVec T) := by
      rw [action.rho_inner]
    _ = if T = V then 1 else 0 := by
      rw [tableauInner_basis_basis_eq_ite]
      by_cases hTV : T = V
      · simp [hTV]
      · have hVT : V ≠ T := Ne.symm hTV
        simp [hTV, hVT]

/-- The conjugation-averaged rank-one operator has the same trace as the
original rank-one operator. -/
theorem youngAveragedRankOne_trace
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam) :
    tableauOperatorTrace (youngAveragedRankOne action T V) =
      if T = V then 1 else 0 := by
  classical
  unfold tableauOperatorTrace youngAveragedRankOne
  calc
    (∑ U : StandardYoungTableau lam,
      ((Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ •
        ∑ g : Perm (Fin (n + 1)),
          youngConjugatedRankOne action T V g (tableauBasisVec U)) U) =
        (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
          ∑ g : Perm (Fin (n + 1)),
            tableauOperatorTrace (youngConjugatedRankOne action T V g) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      calc
        (∑ U : StandardYoungTableau lam,
          (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
            ∑ g : Perm (Fin (n + 1)),
              youngConjugatedRankOne action T V g (tableauBasisVec U) U) =
            ∑ U : StandardYoungTableau lam,
              ∑ g : Perm (Fin (n + 1)),
                (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
                  youngConjugatedRankOne action T V g
                    (tableauBasisVec U) U := by
          apply Finset.sum_congr rfl
          intro U _hU
          rw [Finset.mul_sum]
        _ = ∑ g : Perm (Fin (n + 1)),
            ∑ U : StandardYoungTableau lam,
              (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
                youngConjugatedRankOne action T V g
                  (tableauBasisVec U) U := by
          rw [Finset.sum_comm]
        _ = (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
            ∑ g : Perm (Fin (n + 1)),
              tableauOperatorTrace
                (youngConjugatedRankOne action T V g) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _hg
          unfold tableauOperatorTrace
          rw [Finset.mul_sum]
    _ = (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ *
        ∑ _g : Perm (Fin (n + 1)), (if T = V then 1 else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      rw [youngConjugatedRankOne_trace]
    _ = if T = V then 1 else 0 := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      have hcard :
          (Fintype.card (Perm (Fin (n + 1))) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- A conjugated rank-one operator is additive. -/
theorem youngConjugatedRankOne_map_add
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (g : Perm (Fin (n + 1))) (f h : TableauSpace lam) :
    youngConjugatedRankOne action T V g (f + h) =
      youngConjugatedRankOne action T V g f +
        youngConjugatedRankOne action T V g h := by
  have hrank :
      tableauRankOne T V (action.rep.rho g.symm (f + h)) =
        tableauRankOne T V (action.rep.rho g.symm f) +
          tableauRankOne T V (action.rep.rho g.symm h) := by
    funext U
    rw [action.rep.map_add]
    simp [tableauRankOne]
    ring
  unfold youngConjugatedRankOne
  rw [hrank, action.rep.map_add]

/-- A conjugated rank-one operator is homogeneous. -/
theorem youngConjugatedRankOne_map_smul
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (g : Perm (Fin (n + 1))) (c : ℝ) (f : TableauSpace lam) :
    youngConjugatedRankOne action T V g (c • f) =
      c • youngConjugatedRankOne action T V g f := by
  have hrank :
      tableauRankOne T V (action.rep.rho g.symm (c • f)) =
        c • tableauRankOne T V (action.rep.rho g.symm f) := by
    funext U
    rw [action.rep.map_smul]
    simp [tableauRankOne]
    ring
  unfold youngConjugatedRankOne
  rw [hrank, action.rep.map_smul]

/-- The conjugation-averaged rank-one operator is additive. -/
theorem youngAveragedRankOne_map_add
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (f h : TableauSpace lam) :
    youngAveragedRankOne action T V (f + h) =
      youngAveragedRankOne action T V f +
        youngAveragedRankOne action T V h := by
  classical
  unfold youngAveragedRankOne
  simp_rw [youngConjugatedRankOne_map_add action T V]
  rw [Finset.sum_add_distrib, smul_add]

/-- The conjugation-averaged rank-one operator is homogeneous. -/
theorem youngAveragedRankOne_map_smul
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (c : ℝ) (f : TableauSpace lam) :
    youngAveragedRankOne action T V (c • f) =
      c • youngAveragedRankOne action T V f := by
  classical
  unfold youngAveragedRankOne
  simp_rw [youngConjugatedRankOne_map_smul action T V]
  funext U
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- The averaged rank-one operator, packaged as a linear map. -/
def youngAveragedRankOneLinearMap
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam) :
    TableauSpace lam →ₗ[ℝ] TableauSpace lam where
  toFun := youngAveragedRankOne action T V
  map_add' := youngAveragedRankOne_map_add action T V
  map_smul' := youngAveragedRankOne_map_smul action T V

/-- Relabeling the conjugation summand by left multiplication moves the group
action outside that summand. -/
theorem youngConjugatedRankOne_mul_left
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (h g : Perm (Fin (n + 1))) (f : TableauSpace lam) :
    youngConjugatedRankOne action T V (h * g) (action.rep.rho h f) =
      action.rep.rho h (youngConjugatedRankOne action T V g f) := by
  have hinverse :
      action.rep.rho (h * g).symm (action.rep.rho h f) =
        action.rep.rho g.symm f := by
    rw [show (h * g).symm = g.symm * h.symm by rfl]
    rw [action.rep.map_mul]
    rw [action.rho_leftInverse]
  unfold youngConjugatedRankOne
  rw [hinverse]
  rw [action.rep.map_mul]

/-- The conjugation average commutes with every represented permutation. -/
theorem youngAveragedRankOne_commutes_rho
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (h : Perm (Fin (n + 1))) (f : TableauSpace lam) :
    youngAveragedRankOne action T V (action.rep.rho h f) =
      action.rep.rho h (youngAveragedRankOne action T V f) := by
  classical
  let leftMul : Perm (Fin (n + 1)) ≃ Perm (Fin (n + 1)) := Equiv.mulLeft h
  have hsum :
      (∑ g : Perm (Fin (n + 1)),
        youngConjugatedRankOne action T V g (action.rep.rho h f)) =
        action.rep.rho h
          (∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOne action T V g f) := by
    calc
      (∑ g : Perm (Fin (n + 1)),
        youngConjugatedRankOne action T V g (action.rep.rho h f)) =
          ∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOne action T V (h * g)
              (action.rep.rho h f) := by
        exact (Equiv.sum_comp leftMul
          (fun g : Perm (Fin (n + 1)) =>
            youngConjugatedRankOne action T V g
              (action.rep.rho h f))).symm
      _ = ∑ g : Perm (Fin (n + 1)),
          action.rep.rho h (youngConjugatedRankOne action T V g f) := by
        apply Finset.sum_congr rfl
        intro g _hg
        exact youngConjugatedRankOne_mul_left action T V h g f
      _ = action.rep.rho h
          (∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOne action T V g f) := by
        change
          (∑ g : Perm (Fin (n + 1)),
            (action.rep.linearMap h)
              (youngConjugatedRankOne action T V g f)) =
            (action.rep.linearMap h)
              (∑ g : Perm (Fin (n + 1)),
                youngConjugatedRankOne action T V g f)
        exact
          (map_sum (action.rep.linearMap h)
            (fun g : Perm (Fin (n + 1)) =>
              youngConjugatedRankOne action T V g f)
            Finset.univ).symm
  unfold youngAveragedRankOne
  rw [hsum]
  rw [action.rep.map_smul]

/-- Commutation with every represented group element extends by linearity to
every finite group-algebra element. -/
theorem youngAveragedRankOne_commutes_repOfGroupAlgebra
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (T V : StandardYoungTableau lam)
    (a : GroupAlgebraElement (Perm (Fin (n + 1))))
    (f : TableauSpace lam) :
    youngAveragedRankOne action T V
        (repOfGroupAlgebraElement action.rep a f) =
      repOfGroupAlgebraElement action.rep a
        (youngAveragedRankOne action T V f) := by
  classical
  unfold repOfGroupAlgebraElement
  change
    (youngAveragedRankOneLinearMap action T V)
        (∑ g : Perm (Fin (n + 1)), a g • action.rep.rho g f) =
      ∑ g : Perm (Fin (n + 1)),
        a g • action.rep.rho g (youngAveragedRankOne action T V f)
  calc
    (youngAveragedRankOneLinearMap action T V)
        (∑ g : Perm (Fin (n + 1)), a g • action.rep.rho g f) =
        ∑ g : Perm (Fin (n + 1)),
          (youngAveragedRankOneLinearMap action T V)
            (a g • action.rep.rho g f) := by
      exact map_sum (youngAveragedRankOneLinearMap action T V)
        (fun g : Perm (Fin (n + 1)) => a g • action.rep.rho g f)
        Finset.univ
    _ = ∑ g : Perm (Fin (n + 1)),
        a g • youngAveragedRankOne action T V (action.rep.rho g f) := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact (youngAveragedRankOneLinearMap action T V).map_smul
        (a g) (action.rep.rho g f)
    _ = ∑ g : Perm (Fin (n + 1)),
        a g • action.rep.rho g (youngAveragedRankOne action T V f) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [youngAveragedRankOne_commutes_rho]

/-- The averaged rank-one operator supplies the hypotheses of the internally
proved Young-basis scalar commutant theorem. -/
def youngAveragedRankOneCommutationData
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T V : StandardYoungTableau lam) :
    YoungModelOperatorCommutationData lam where
  op := youngAveragedRankOne action T V
  map_add := youngAveragedRankOne_map_add action T V
  map_smul := by
    intro c f
    exact youngAveragedRankOne_map_smul action T V c f
  commutes_adjacent := by
    intro a f
    rw [← action.rho_adjacent a f]
    rw [youngAveragedRankOne_commutes_rho]
    rw [action.rho_adjacent]
  commutes_content := by
    intro a f
    calc
      youngAveragedRankOne action T V
          (jucysMurphyDiagonalOperator a f) =
          youngAveragedRankOne action T V
            (repOfGroupAlgebraElement action.rep
              (s05_jucysMurphyElement a) f) := by
        simpa [repOfGroupAlgebraElement] using
          congrArg (youngAveragedRankOne action T V)
            (content.rho_content a f).symm
      _ = repOfGroupAlgebraElement action.rep
          (s05_jucysMurphyElement a)
            (youngAveragedRankOne action T V f) := by
        exact youngAveragedRankOne_commutes_repOfGroupAlgebra
          action T V (s05_jucysMurphyElement a) f
      _ = jucysMurphyDiagonalOperator a
          (youngAveragedRankOne action T V f) := by
        simpa [repOfGroupAlgebraElement] using
          content.rho_content a (youngAveragedRankOne action T V f)

/-- The conjugation-averaged rank-one operator is scalar on every tableau
basis vector. -/
theorem youngAveragedRankOne_scalar_on_basis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T V T0 U : StandardYoungTableau lam) :
    youngAveragedRankOne action T V (tableauBasisVec U) =
      fun W =>
        (youngAveragedRankOneCommutationData action content T V).basisScalar T0 *
          tableauBasisVec U W := by
  exact S05_Lem5_05_youngModelOperator_scalar_on_basis
    (youngAveragedRankOneCommutationData action content T V) T0 U

/-- The trace determines the scalar of the conjugation-averaged rank-one
operator. -/
theorem youngAveragedRankOne_basisScalar
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T V T0 : StandardYoungTableau lam) :
    (youngAveragedRankOneCommutationData action content T V).basisScalar T0 =
      (if T = V then 1 else 0) / tableauDim lam := by
  let c :=
    (youngAveragedRankOneCommutationData action content T V).basisScalar T0
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  calc
    c = tableauOperatorTrace (youngAveragedRankOne action T V) /
        tableauDim lam := by
      apply scalar_eq_tableauOperatorTrace_div_tableauDim
        (youngAveragedRankOne action T V) c hdim
      intro U
      exact youngAveragedRankOne_scalar_on_basis
        action content T V T0 U
    _ = (if T = V then 1 else 0) / tableauDim lam := by
      rw [youngAveragedRankOne_trace]

/-- One matrix entry of a conjugated rank-one operator is the product of the
corresponding two Young matrix coefficients. -/
theorem youngConjugatedRankOne_basis_coordinate
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (S T U V : StandardYoungTableau lam)
    (g : Perm (Fin (n + 1))) :
    youngConjugatedRankOne action T V g (tableauBasisVec U) S =
      youngMatrixCoefficient action S T g *
        youngMatrixCoefficient action U V g := by
  unfold youngConjugatedRankOne tableauRankOne
  change action.rep.rho g
      (action.rep.rho g.symm (tableauBasisVec U) V • tableauBasisVec T) S = _
  rw [action.rep.map_smul]
  rw [rho_symm_basis_coordinate]
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold youngMatrixCoefficient
  rw [tableauInner_left_basis, tableauInner_left_basis]
  ring

/-- The normalized product of two matrix coefficients is a matrix entry of
the conjugation-averaged rank-one operator. -/
theorem permInner_youngMatrixCoefficient_eq_averagedRankOne_coordinate
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (S T U V : StandardYoungTableau lam) :
    permInner (youngMatrixCoefficient action S T)
        (youngMatrixCoefficient action U V) =
      youngAveragedRankOne action T V (tableauBasisVec U) S := by
  classical
  unfold permInner youngAveragedRankOne
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [youngConjugatedRankOne_basis_coordinate action S T U V]
  rw [div_eq_mul_inv]
  ring

/-- Schur orthogonality for matrix coefficients belonging to one concrete
Young action.  The proof is the explicit averaged-rank-one argument above. -/
theorem youngMatrixCoefficient_orthogonality_same_shape
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (S T U V : StandardYoungTableau lam) :
    permInner (youngMatrixCoefficient action S T)
        (youngMatrixCoefficient action U V) =
      if S = U ∧ T = V then 1 / tableauDim lam else 0 := by
  rw [permInner_youngMatrixCoefficient_eq_averagedRankOne_coordinate]
  have hscalar := congrFun
    (youngAveragedRankOne_scalar_on_basis
      action content T V T U) S
  rw [hscalar]
  rw [youngAveragedRankOne_basisScalar action content T V T]
  by_cases hSU : S = U
  · subst U
    by_cases hTV : T = V
    · subst V
      simp [tableauBasisVec]
    · simp [hTV, tableauBasisVec]
  · simp [hSU, tableauBasisVec]

/-- A rank-one map between two tableau spaces of the same symmetric-group
size. -/
def tableauRankOneBetween
    {n : Nat} {lam mu : YoungDiagram n}
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu) :
    TableauSpace mu → TableauSpace lam :=
  fun f U => f V * tableauBasisVec T U

/-- Conjugate a cross-shape rank-one map by two supplied Young actions. -/
def youngConjugatedRankOneBetween
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (g : Perm (Fin (n + 1))) :
    TableauSpace mu → TableauSpace lam :=
  fun f =>
    actionLam.rep.rho g
      (tableauRankOneBetween T V (actionMu.rep.rho g.symm f))

/-- Uniform conjugation average of a cross-shape rank-one map. -/
def youngAveragedRankOneBetween
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu) :
    TableauSpace mu → TableauSpace lam :=
  fun f =>
    (Fintype.card (Perm (Fin (n + 1))) : ℝ)⁻¹ •
      ∑ g : Perm (Fin (n + 1)),
        youngConjugatedRankOneBetween actionLam actionMu T V g f

theorem youngConjugatedRankOneBetween_map_add
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (g : Perm (Fin (n + 1))) (f h : TableauSpace mu) :
    youngConjugatedRankOneBetween actionLam actionMu T V g (f + h) =
      youngConjugatedRankOneBetween actionLam actionMu T V g f +
        youngConjugatedRankOneBetween actionLam actionMu T V g h := by
  have hrank :
      tableauRankOneBetween T V (actionMu.rep.rho g.symm (f + h)) =
        tableauRankOneBetween T V (actionMu.rep.rho g.symm f) +
          tableauRankOneBetween T V (actionMu.rep.rho g.symm h) := by
    funext U
    rw [actionMu.rep.map_add]
    simp [tableauRankOneBetween]
    ring
  unfold youngConjugatedRankOneBetween
  rw [hrank, actionLam.rep.map_add]

theorem youngConjugatedRankOneBetween_map_smul
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (g : Perm (Fin (n + 1))) (c : ℝ) (f : TableauSpace mu) :
    youngConjugatedRankOneBetween actionLam actionMu T V g (c • f) =
      c • youngConjugatedRankOneBetween actionLam actionMu T V g f := by
  have hrank :
      tableauRankOneBetween T V (actionMu.rep.rho g.symm (c • f)) =
        c • tableauRankOneBetween T V (actionMu.rep.rho g.symm f) := by
    funext U
    rw [actionMu.rep.map_smul]
    simp [tableauRankOneBetween]
    ring
  unfold youngConjugatedRankOneBetween
  rw [hrank, actionLam.rep.map_smul]

theorem youngAveragedRankOneBetween_map_add
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (f h : TableauSpace mu) :
    youngAveragedRankOneBetween actionLam actionMu T V (f + h) =
      youngAveragedRankOneBetween actionLam actionMu T V f +
        youngAveragedRankOneBetween actionLam actionMu T V h := by
  classical
  unfold youngAveragedRankOneBetween
  simp_rw [youngConjugatedRankOneBetween_map_add
    actionLam actionMu T V]
  rw [Finset.sum_add_distrib, smul_add]

theorem youngAveragedRankOneBetween_map_smul
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (c : ℝ) (f : TableauSpace mu) :
    youngAveragedRankOneBetween actionLam actionMu T V (c • f) =
      c • youngAveragedRankOneBetween actionLam actionMu T V f := by
  classical
  unfold youngAveragedRankOneBetween
  simp_rw [youngConjugatedRankOneBetween_map_smul
    actionLam actionMu T V]
  funext U
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

def youngAveragedRankOneBetweenLinearMap
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu) :
    TableauSpace mu →ₗ[ℝ] TableauSpace lam where
  toFun := youngAveragedRankOneBetween actionLam actionMu T V
  map_add' := youngAveragedRankOneBetween_map_add actionLam actionMu T V
  map_smul' := youngAveragedRankOneBetween_map_smul actionLam actionMu T V

theorem youngConjugatedRankOneBetween_mul_left
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (h g : Perm (Fin (n + 1))) (f : TableauSpace mu) :
    youngConjugatedRankOneBetween actionLam actionMu T V (h * g)
        (actionMu.rep.rho h f) =
      actionLam.rep.rho h
        (youngConjugatedRankOneBetween actionLam actionMu T V g f) := by
  have hinverse :
      actionMu.rep.rho (h * g).symm (actionMu.rep.rho h f) =
        actionMu.rep.rho g.symm f := by
    rw [show (h * g).symm = g.symm * h.symm by rfl]
    rw [actionMu.rep.map_mul]
    rw [actionMu.rho_leftInverse]
  unfold youngConjugatedRankOneBetween
  rw [hinverse]
  rw [actionLam.rep.map_mul]

theorem youngAveragedRankOneBetween_commutes_rho
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (h : Perm (Fin (n + 1))) (f : TableauSpace mu) :
    youngAveragedRankOneBetween actionLam actionMu T V
        (actionMu.rep.rho h f) =
      actionLam.rep.rho h
        (youngAveragedRankOneBetween actionLam actionMu T V f) := by
  classical
  let leftMul : Perm (Fin (n + 1)) ≃ Perm (Fin (n + 1)) := Equiv.mulLeft h
  have hsum :
      (∑ g : Perm (Fin (n + 1)),
        youngConjugatedRankOneBetween actionLam actionMu T V g
          (actionMu.rep.rho h f)) =
        actionLam.rep.rho h
          (∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOneBetween actionLam actionMu T V g f) := by
    calc
      (∑ g : Perm (Fin (n + 1)),
        youngConjugatedRankOneBetween actionLam actionMu T V g
          (actionMu.rep.rho h f)) =
          ∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOneBetween actionLam actionMu T V (h * g)
              (actionMu.rep.rho h f) := by
        exact (Equiv.sum_comp leftMul
          (fun g : Perm (Fin (n + 1)) =>
            youngConjugatedRankOneBetween actionLam actionMu T V g
              (actionMu.rep.rho h f))).symm
      _ = ∑ g : Perm (Fin (n + 1)),
          actionLam.rep.rho h
            (youngConjugatedRankOneBetween actionLam actionMu T V g f) := by
        apply Finset.sum_congr rfl
        intro g _hg
        exact youngConjugatedRankOneBetween_mul_left
          actionLam actionMu T V h g f
      _ = actionLam.rep.rho h
          (∑ g : Perm (Fin (n + 1)),
            youngConjugatedRankOneBetween actionLam actionMu T V g f) := by
        change
          (∑ g : Perm (Fin (n + 1)),
            (actionLam.rep.linearMap h)
              (youngConjugatedRankOneBetween actionLam actionMu T V g f)) =
            (actionLam.rep.linearMap h)
              (∑ g : Perm (Fin (n + 1)),
                youngConjugatedRankOneBetween actionLam actionMu T V g f)
        exact
          (map_sum (actionLam.rep.linearMap h)
            (fun g : Perm (Fin (n + 1)) =>
              youngConjugatedRankOneBetween actionLam actionMu T V g f)
            Finset.univ).symm
  unfold youngAveragedRankOneBetween
  rw [hsum]
  rw [actionLam.rep.map_smul]

theorem youngAveragedRankOneBetween_commutes_repOfGroupAlgebra
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (a : GroupAlgebraElement (Perm (Fin (n + 1))))
    (f : TableauSpace mu) :
    youngAveragedRankOneBetween actionLam actionMu T V
        (repOfGroupAlgebraElement actionMu.rep a f) =
      repOfGroupAlgebraElement actionLam.rep a
        (youngAveragedRankOneBetween actionLam actionMu T V f) := by
  classical
  unfold repOfGroupAlgebraElement
  change
    (youngAveragedRankOneBetweenLinearMap actionLam actionMu T V)
        (∑ g : Perm (Fin (n + 1)), a g • actionMu.rep.rho g f) =
      ∑ g : Perm (Fin (n + 1)),
        a g • actionLam.rep.rho g
          (youngAveragedRankOneBetween actionLam actionMu T V f)
  calc
    (youngAveragedRankOneBetweenLinearMap actionLam actionMu T V)
        (∑ g : Perm (Fin (n + 1)), a g • actionMu.rep.rho g f) =
        ∑ g : Perm (Fin (n + 1)),
          (youngAveragedRankOneBetweenLinearMap actionLam actionMu T V)
            (a g • actionMu.rep.rho g f) := by
      exact map_sum
        (youngAveragedRankOneBetweenLinearMap actionLam actionMu T V)
        (fun g : Perm (Fin (n + 1)) => a g • actionMu.rep.rho g f)
        Finset.univ
    _ = ∑ g : Perm (Fin (n + 1)),
        a g • youngAveragedRankOneBetween actionLam actionMu T V
          (actionMu.rep.rho g f) := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact
        (youngAveragedRankOneBetweenLinearMap actionLam actionMu T V).map_smul
          (a g) (actionMu.rep.rho g f)
    _ = ∑ g : Perm (Fin (n + 1)),
        a g • actionLam.rep.rho g
          (youngAveragedRankOneBetween actionLam actionMu T V f) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [youngAveragedRankOneBetween_commutes_rho]

/-- The cross-shape conjugation average intertwines the two concrete diagonal
content actions. -/
theorem youngAveragedRankOneBetween_intertwines_content
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    (T : StandardYoungTableau lam) (V : StandardYoungTableau mu)
    (a : Fin (n + 1)) (f : TableauSpace mu) :
    youngAveragedRankOneBetween actionLam actionMu T V
        (jucysMurphyDiagonalOperator a f) =
      jucysMurphyDiagonalOperator a
        (youngAveragedRankOneBetween actionLam actionMu T V f) := by
  calc
    youngAveragedRankOneBetween actionLam actionMu T V
        (jucysMurphyDiagonalOperator a f) =
        youngAveragedRankOneBetween actionLam actionMu T V
          (repOfGroupAlgebraElement actionMu.rep
            (s05_jucysMurphyElement a) f) := by
      simpa [repOfGroupAlgebraElement] using
        congrArg (youngAveragedRankOneBetween actionLam actionMu T V)
          (contentMu.rho_content a f).symm
    _ = repOfGroupAlgebraElement actionLam.rep
        (s05_jucysMurphyElement a)
          (youngAveragedRankOneBetween actionLam actionMu T V f) := by
      exact youngAveragedRankOneBetween_commutes_repOfGroupAlgebra
        actionLam actionMu T V (s05_jucysMurphyElement a) f
    _ = jucysMurphyDiagonalOperator a
        (youngAveragedRankOneBetween actionLam actionMu T V f) := by
      simpa [repOfGroupAlgebraElement] using
        contentLam.rho_content a
          (youngAveragedRankOneBetween actionLam actionMu T V f)

/-- A cross-shape averaged rank-one image of a source basis vector is a common
content eigenvector with the source tableau's content sequence. -/
theorem youngAveragedRankOneBetween_basis_content_eigen
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    (T : StandardYoungTableau lam) (V U : StandardYoungTableau mu)
    (a : Fin (n + 1)) :
    jucysMurphyDiagonalOperator a
        (youngAveragedRankOneBetween actionLam actionMu T V
          (tableauBasisVec U)) =
      fun S => (entryContent U a : ℝ) *
        youngAveragedRankOneBetween actionLam actionMu T V
          (tableauBasisVec U) S := by
  rw [← youngAveragedRankOneBetween_intertwines_content
    actionLam contentLam actionMu contentMu T V a]
  rw [jucysMurphyDiagonalOperator_basis_eigen]
  exact youngAveragedRankOneBetween_map_smul
    actionLam actionMu T V (entryContent U a : ℝ) (tableauBasisVec U)

/-- If a target coordinate has the wrong content eigenvalue, that coordinate
of a cross-shape eigenvector vanishes. -/
theorem diagonalContent_external_eigen_coordinate_zero
    {n : Nat} {lam : YoungDiagram n}
    (S : StandardYoungTableau lam) (f : TableauSpace lam)
    (a : Fin n) (c : Int)
    (hf : jucysMurphyDiagonalOperator a f = fun W => (c : ℝ) * f W)
    (hne : entryContent S a ≠ c) :
    f S = 0 := by
  have hcoord := congrFun hf S
  change (entryContent S a : ℝ) * f S = (c : ℝ) * f S at hcoord
  have hcoeff : (entryContent S a : ℝ) - (c : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hne
  have hzero : ((entryContent S a : ℝ) - (c : ℝ)) * f S = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hzero).resolve_left hcoeff

/-- Tableaux of distinct shapes differ in at least one entry content. -/
theorem exists_entryContent_ne_of_shape_ne
    {n : Nat} {lam mu : YoungDiagram n}
    (hshape : lam ≠ mu)
    (S : StandardYoungTableau lam) (U : StandardYoungTableau mu) :
    ∃ a : Fin n, entryContent S a ≠ entryContent U a := by
  by_contra hnone
  apply hshape
  apply tableauContentSequence_determines_shape S U
  funext a
  by_contra hne
  exact hnone ⟨a, by simpa [tableauContentSequence] using hne⟩

/-- A cross-shape averaged rank-one map vanishes on each source basis vector
when the two Young shapes are distinct. -/
theorem youngAveragedRankOneBetween_basis_eq_zero_of_shape_ne
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (hshape : lam ≠ mu)
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    (T : StandardYoungTableau lam) (V U : StandardYoungTableau mu) :
    youngAveragedRankOneBetween actionLam actionMu T V
        (tableauBasisVec U) = 0 := by
  funext S
  rcases exists_entryContent_ne_of_shape_ne hshape S U with ⟨a, hne⟩
  exact diagonalContent_external_eigen_coordinate_zero S
    (youngAveragedRankOneBetween actionLam actionMu T V (tableauBasisVec U))
    a (entryContent U a)
    (youngAveragedRankOneBetween_basis_content_eigen
      actionLam contentLam actionMu contentMu T V U a)
    hne

theorem youngConjugatedRankOneBetween_basis_coordinate
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (S T : StandardYoungTableau lam)
    (U V : StandardYoungTableau mu)
    (g : Perm (Fin (n + 1))) :
    youngConjugatedRankOneBetween actionLam actionMu T V g
        (tableauBasisVec U) S =
      youngMatrixCoefficient actionLam S T g *
        youngMatrixCoefficient actionMu U V g := by
  unfold youngConjugatedRankOneBetween tableauRankOneBetween
  change actionLam.rep.rho g
      (actionMu.rep.rho g.symm (tableauBasisVec U) V • tableauBasisVec T) S = _
  rw [actionLam.rep.map_smul]
  rw [rho_symm_basis_coordinate]
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold youngMatrixCoefficient
  rw [tableauInner_left_basis, tableauInner_left_basis]
  ring

theorem permInner_youngMatrixCoefficient_eq_averagedRankOneBetween_coordinate
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (actionLam : YoungOrthogonalActionData lam)
    (actionMu : YoungOrthogonalActionData mu)
    (S T : StandardYoungTableau lam)
    (U V : StandardYoungTableau mu) :
    permInner (youngMatrixCoefficient actionLam S T)
        (youngMatrixCoefficient actionMu U V) =
      youngAveragedRankOneBetween actionLam actionMu T V
        (tableauBasisVec U) S := by
  classical
  unfold permInner youngAveragedRankOneBetween
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [youngConjugatedRankOneBetween_basis_coordinate
    actionLam actionMu S T U V]
  rw [div_eq_mul_inv]
  ring

/-- Matrix-coefficient blocks attached to distinct Young shapes are
orthogonal. -/
theorem youngMatrixCoefficient_orthogonality_distinct_shapes
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (hshape : lam ≠ mu)
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    (S T : StandardYoungTableau lam)
    (U V : StandardYoungTableau mu) :
    permInner (youngMatrixCoefficient actionLam S T)
        (youngMatrixCoefficient actionMu U V) = 0 := by
  rw [permInner_youngMatrixCoefficient_eq_averagedRankOneBetween_coordinate]
  rw [youngAveragedRankOneBetween_basis_eq_zero_of_shape_ne
    hshape actionLam contentLam actionMu contentMu T V U]
  rfl

/-- Index type for all Young matrix coefficients at one symmetric-group
size. -/
abbrev YoungMatrixCoefficientIndex (n : Nat) :=
  Sigma fun lam : YoungDiagram n =>
    StandardYoungTableau lam × StandardYoungTableau lam

/-- The global family of matrix coefficients supplied by one faithful Young
action for each shape. -/
def globalYoungMatrixCoefficient
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (i : YoungMatrixCoefficientIndex (n + 1)) :
    Perm (Fin (n + 1)) → ℝ :=
  youngMatrixCoefficient (action i.1) i.2.1 i.2.2

/-- Orthogonality formula for the global matrix-coefficient family, combining
the same-shape and distinct-shape arguments. -/
theorem globalYoungMatrixCoefficient_orthogonality
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (i j : YoungMatrixCoefficientIndex (n + 1)) :
    permInner (globalYoungMatrixCoefficient action i)
        (globalYoungMatrixCoefficient action j) =
      if i = j then 1 / tableauDim i.1 else 0 := by
  rcases i with ⟨lam, ⟨S, T⟩⟩
  rcases j with ⟨mu, ⟨U, V⟩⟩
  dsimp [globalYoungMatrixCoefficient]
  by_cases hshape : lam = mu
  · subst mu
    rw [youngMatrixCoefficient_orthogonality_same_shape
      (action lam) (content lam) S T U V]
    by_cases hS : S = U
    · subst U
      by_cases hT : T = V
      · subst V
        simp
      · simp [hT]
    · simp [hS]
  · rw [youngMatrixCoefficient_orthogonality_distinct_shapes
      hshape (action lam) (content lam) (action mu) (content mu) S T U V]
    simp [hshape]

/-- `permInner` is linear in a finite sum in its first argument. -/
theorem permInner_fintype_sum_smul_left
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (c : ι → ℝ) (F : ι → Perm α → ℝ) (H : Perm α → ℝ) :
    permInner (∑ i : ι, c i • F i) H =
      ∑ i : ι, c i * permInner (F i) H := by
  classical
  unfold permInner
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ π : Perm α, (∑ i : ι, c i * F i π) * H π) /
        (Fintype.card (Perm α) : ℝ) =
        (∑ i : ι, c i * ∑ π : Perm α, F i π * H π) /
          (Fintype.card (Perm α) : ℝ) := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _hπ
      ring
    _ = ∑ i : ι,
        c i * ((∑ π : Perm α, F i π * H π) /
          (Fintype.card (Perm α) : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- The global Young matrix coefficients are linearly independent.  This is
already stronger than a within-block statement and uses no dimension count. -/
theorem globalYoungMatrixCoefficient_linearIndependent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    LinearIndependent ℝ (globalYoungMatrixCoefficient action) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  have hinner := congrArg
    (fun F => permInner F (globalYoungMatrixCoefficient action x)) hc
  rw [permInner_fintype_sum_smul_left] at hinner
  have hzero :
      permInner (0 : Perm (Fin (n + 1)) → ℝ)
        (globalYoungMatrixCoefficient action x) = 0 := by
    simp [permInner]
  rw [hzero] at hinner
  simp_rw [globalYoungMatrixCoefficient_orthogonality action content] at hinner
  have hsingle :
      (∑ i : YoungMatrixCoefficientIndex (n + 1),
        c i * (if i = x then 1 / tableauDim i.1 else 0)) =
          c x * (1 / tableauDim x.1) := by
    rw [Fintype.sum_eq_single x]
    · simp
    · intro i hix
      simp [hix]
  rw [hsingle] at hinner
  have hdim : tableauDim x.1 ≠ 0 :=
    tableauDim_ne_zero_of_tableau x.2.1
  have hfactor : (1 / tableauDim x.1 : ℝ) ≠ 0 :=
    div_ne_zero one_ne_zero hdim
  exact (mul_eq_zero.mp hinner).resolve_right hfactor

/-- Cardinality of the global coefficient index is the sum of the squared
tableau dimensions. -/
theorem card_youngMatrixCoefficientIndex
    (n : Nat) :
    Fintype.card (YoungMatrixCoefficientIndex n) =
      ∑ lam : YoungDiagram n, (tableauDimNat lam) ^ 2 := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro lam _hlam
  rw [Fintype.card_prod]
  rw [tableauDimNat_eq_card]
  ring

/-- The global Young matrix-coefficient index has exactly as many elements as
the symmetric group. -/
theorem card_YoungMatrixCoefficientIndex_eq_perm (n : Nat) :
    Fintype.card (YoungMatrixCoefficientIndex n) =
      Fintype.card (Perm (Fin n)) := by
  rw [card_youngMatrixCoefficientIndex,
    sum_tableauDimNat_sq_eq_factorial, Fintype.card_perm]
  simp

/-- A supplied cardinality equality makes the global matrix-coefficient family
span all group functions.  The unconditional corollary below supplies this
equality from the internal Young-tableau sum-of-squares theorem. -/
theorem globalYoungMatrixCoefficient_span_all_of_card_eq
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (hcard :
      Fintype.card (YoungMatrixCoefficientIndex (n + 1)) =
        Fintype.card (Perm (Fin (n + 1)))) :
    Submodule.span ℝ
        (Set.range (globalYoungMatrixCoefficient action)) = ⊤ := by
  apply
    (globalYoungMatrixCoefficient_linearIndependent action content).span_eq_top_of_card_eq_finrank'
  rw [hcard]
  exact (Module.finrank_pi ℝ :
    Module.finrank ℝ (Perm (Fin (n + 1)) → ℝ) =
      Fintype.card (Perm (Fin (n + 1)))).symm

/-- The global Young matrix coefficients span all functions on the symmetric
group. -/
theorem globalYoungMatrixCoefficient_span_all
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    Submodule.span ℝ
        (Set.range (globalYoungMatrixCoefficient action)) = ⊤ :=
  globalYoungMatrixCoefficient_span_all_of_card_eq action content
    (card_YoungMatrixCoefficientIndex_eq_perm (n + 1))

/-- The concrete global matrix-coefficient basis. -/
noncomputable def regularYoungMatrixCoefficientBasis
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam)) :
    Module.Basis (YoungMatrixCoefficientIndex (n + 1)) ℝ
      (Perm (Fin (n + 1)) → ℝ) :=
  Module.Basis.mk
    (globalYoungMatrixCoefficient_linearIndependent action content) (by
    rw [globalYoungMatrixCoefficient_span_all action content])

/-- The actual component of a group function in one concrete Young
matrix-coefficient block. -/
noncomputable def concreteYoungBlockComponent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ)
    (lam : YoungDiagram (n + 1)) :
    Perm (Fin (n + 1)) → ℝ :=
  ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
    (regularYoungMatrixCoefficientBasis action content).repr F
        ⟨lam, ST⟩ •
      globalYoungMatrixCoefficient action ⟨lam, ST⟩

/-- A concrete shape component belongs to its matrix-coefficient block. -/
theorem concreteYoungBlockComponent_mem
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) -> Real)
    (lam : YoungDiagram (n + 1)) :
    concreteYoungBlockComponent action content F lam ∈
      youngMatrixCoefficientBlock (action lam) := by
  classical
  unfold concreteYoungBlockComponent
  apply Submodule.sum_mem
  intro ST _hST
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨ST, rfl⟩

/-- The concrete Young-block components sum to the original group function. -/
theorem sum_concreteYoungBlockComponent
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    (∑ lam : YoungDiagram (n + 1),
      concreteYoungBlockComponent action content F lam) = F := by
  unfold concreteYoungBlockComponent
  simpa [Fintype.sum_sigma, regularYoungMatrixCoefficientBasis,
    Module.Basis.mk_apply] using
    (regularYoungMatrixCoefficientBasis action content).sum_repr F

/-- The normalized inner product on group functions is symmetric. -/
theorem permInner_symm
    {α : Type*} [Fintype α] [DecidableEq α]
    (F H : Perm α → ℝ) :
    permInner F H = permInner H F := by
  unfold permInner
  congr 1
  apply Finset.sum_congr rfl
  intro π _hπ
  ring

@[simp] theorem permInner_zero_left
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α -> Real) :
    permInner 0 F = 0 := by
  simp [permInner]

@[simp] theorem permInner_zero_right
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α -> Real) :
    permInner F 0 = 0 := by
  simp [permInner]

theorem permInner_add_left
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G H : Perm α -> Real) :
    permInner (F + G) H = permInner F H + permInner G H := by
  unfold permInner
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem permInner_add_right
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G H : Perm α -> Real) :
    permInner F (G + H) = permInner F G + permInner F H := by
  rw [permInner_symm, permInner_add_left]
  rw [permInner_symm F G, permInner_symm F H]

theorem permInner_smul_left
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : Real) (F G : Perm α -> Real) :
    permInner (c • F) G = c * permInner F G := by
  unfold permInner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ pi : Perm α, c * F pi * G pi) /
        (Fintype.card (Perm α) : Real) =
        (c * ∑ pi : Perm α, F pi * G pi) /
          (Fintype.card (Perm α) : Real) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro pi _hpi
      ring
    _ = c * ((∑ pi : Perm α, F pi * G pi) /
          (Fintype.card (Perm α) : Real)) := by
      ring

theorem permInner_smul_right
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : Real) (F G : Perm α -> Real) :
    permInner F (c • G) = c * permInner F G := by
  rw [permInner_symm, permInner_smul_left, permInner_symm G F]

theorem permInner_sub_left
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G H : Perm α -> Real) :
    permInner (F - G) H = permInner F H - permInner G H := by
  unfold permInner
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem permInner_sub_right
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G H : Perm α -> Real) :
    permInner F (G - H) = permInner F G - permInner F H := by
  rw [permInner_symm, permInner_sub_left]
  rw [permInner_symm G F, permInner_symm H F]

/-- Squared distance is the normalized inner product of the difference with
itself. -/
theorem l2DistSq_eq_permInner_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α -> Real) :
    l2DistSq F G = permInner (F - G) (F - G) := by
  unfold l2DistSq permInner
  congr 1
  apply Finset.sum_congr rfl
  intro pi _hpi
  simp only [Pi.sub_apply]
  ring

/-- The normalized inner product of a real function with itself is
nonnegative. -/
theorem permInner_self_nonnegative
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α -> Real) :
    0 ≤ permInner F F := by
  unfold permInner
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro pi _hpi
    exact mul_self_nonneg (F pi)
  · have hcard : 0 < (Fintype.card (Perm α) : Real) := by
      exact_mod_cast
        (Fintype.card_pos_iff.mpr
          ⟨(1 : Perm α)⟩ : 0 < Fintype.card (Perm α))
    exact hcard.le

/-- `permInner` is linear in a finite sum in its second argument. -/
theorem permInner_fintype_sum_smul_right
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (c : ι → ℝ) (F : ι → Perm α → ℝ) (H : Perm α → ℝ) :
    permInner H (∑ i : ι, c i • F i) =
      ∑ i : ι, c i * permInner H (F i) := by
  calc
    permInner H (∑ i : ι, c i • F i) =
        permInner (∑ i : ι, c i • F i) H :=
      permInner_symm _ _
    _ = ∑ i : ι, c i * permInner (F i) H :=
      permInner_fintype_sum_smul_left c F H
    _ = ∑ i : ι, c i * permInner H (F i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [permInner_symm]

/-- Concrete matrix-coefficient blocks of distinct Young shapes are
orthogonal. -/
theorem youngMatrixCoefficientBlock_orthogonal
    {n : Nat} {lam mu : YoungDiagram (n + 1)}
    (hshape : lam ≠ mu)
    (actionLam : YoungOrthogonalActionData lam)
    (contentLam : JucysMurphyContentActionData actionLam)
    (actionMu : YoungOrthogonalActionData mu)
    (contentMu : JucysMurphyContentActionData actionMu)
    {F G : Perm (Fin (n + 1)) -> Real}
    (hF : F ∈ youngMatrixCoefficientBlock actionLam)
    (hG : G ∈ youngMatrixCoefficientBlock actionMu) :
    permInner F G = 0 := by
  refine Submodule.span_induction
    (p := fun F _ => permInner F G = 0) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨ST, rfl⟩
    refine Submodule.span_induction
      (p := fun G _ =>
        permInner (youngMatrixCoefficient actionLam ST.1 ST.2) G = 0)
      ?_ ?_ ?_ ?_ hG
    · rintro _ ⟨UV, rfl⟩
      exact youngMatrixCoefficient_orthogonality_distinct_shapes
        hshape actionLam contentLam actionMu contentMu
          ST.1 ST.2 UV.1 UV.2
    · exact permInner_zero_right _
    · intro G₁ G₂ _hG₁ _hG₂ h₁ h₂
      rw [permInner_add_right, h₁, h₂, add_zero]
    · intro c G _hG h
      rw [permInner_smul_right, h, mul_zero]
  · exact permInner_zero_left _
  · intro F₁ F₂ _hF₁ _hF₂ h₁ h₂
    rw [permInner_add_left, h₁, h₂, add_zero]
  · intro c F _hF h
    rw [permInner_smul_left, h, mul_zero]

/-- Concrete components belonging to distinct Young shapes are orthogonal. -/
theorem concreteYoungBlockComponent_orthogonal
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ)
    {lam mu : YoungDiagram (n + 1)} (hshape : lam ≠ mu) :
    permInner (concreteYoungBlockComponent action content F lam)
        (concreteYoungBlockComponent action content F mu) = 0 := by
  unfold concreteYoungBlockComponent
  rw [permInner_fintype_sum_smul_left]
  apply Finset.sum_eq_zero
  intro ST _hST
  rw [permInner_fintype_sum_smul_right]
  have hinner :
      (∑ UV : StandardYoungTableau mu × StandardYoungTableau mu,
        ((regularYoungMatrixCoefficientBasis action content).repr F)
            ⟨mu, UV⟩ *
          permInner (globalYoungMatrixCoefficient action ⟨lam, ST⟩)
            (globalYoungMatrixCoefficient action ⟨mu, UV⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro UV _hUV
    change
      ((regularYoungMatrixCoefficientBasis action content).repr F)
          ⟨mu, UV⟩ *
        permInner (youngMatrixCoefficient (action lam) ST.1 ST.2)
          (youngMatrixCoefficient (action mu) UV.1 UV.2) = 0
    rw [youngMatrixCoefficient_orthogonality_distinct_shapes
      hshape (action lam) (content lam) (action mu) (content mu)
        ST.1 ST.2 UV.1 UV.2]
    ring
  rw [hinner]
  ring

/-- Squared norm of the actual component in one concrete Young block. -/
noncomputable def concreteYoungBlockEnergy
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ)
    (lam : YoungDiagram (n + 1)) : ℝ :=
  permInner (concreteYoungBlockComponent action content F lam)
    (concreteYoungBlockComponent action content F lam)

/-- Concrete Young-block energies are nonnegative. -/
theorem concreteYoungBlockEnergy_nonnegative
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ)
    (lam : YoungDiagram (n + 1)) :
    0 ≤ concreteYoungBlockEnergy action content F lam := by
  unfold concreteYoungBlockEnergy permInner
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro π _hπ
    exact mul_self_nonneg _
  · positivity

/-- Parseval decomposition for the actual concrete Young-block components. -/
theorem permInner_self_eq_sum_concreteYoungBlockEnergy
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ) :
    permInner F F =
      ∑ lam : YoungDiagram (n + 1),
        concreteYoungBlockEnergy action content F lam := by
  let component := concreteYoungBlockComponent action content F
  have hsum : (∑ lam : YoungDiagram (n + 1), component lam) = F :=
    sum_concreteYoungBlockComponent action content F
  calc
    permInner F F =
        permInner (∑ lam : YoungDiagram (n + 1), component lam)
          (∑ mu : YoungDiagram (n + 1), component mu) := by
      rw [hsum]
    _ = ∑ lam : YoungDiagram (n + 1),
        permInner (component lam)
          (∑ mu : YoungDiagram (n + 1), component mu) := by
      simpa using
        permInner_fintype_sum_smul_left
          (fun _lam : YoungDiagram (n + 1) => (1 : ℝ)) component
          (∑ mu : YoungDiagram (n + 1), component mu)
    _ = ∑ lam : YoungDiagram (n + 1),
        ∑ mu : YoungDiagram (n + 1),
          permInner (component lam) (component mu) := by
      apply Finset.sum_congr rfl
      intro lam _hlam
      simpa using
        permInner_fintype_sum_smul_right
          (fun _mu : YoungDiagram (n + 1) => (1 : ℝ)) component
          (component lam)
    _ = ∑ lam : YoungDiagram (n + 1),
        permInner (component lam) (component lam) := by
      apply Finset.sum_congr rfl
      intro lam _hlam
      rw [Fintype.sum_eq_single lam]
      intro mu hmulam
      exact concreteYoungBlockComponent_orthogonal
        action content F (Ne.symm hmulam)
    _ = ∑ lam : YoungDiagram (n + 1),
        concreteYoungBlockEnergy action content F lam := by
      rfl


end DictatorshipTesting
