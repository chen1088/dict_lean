import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.Defs.S05_Def5_07_YoungBlockEnergyProfile
import DictatorshipTesting.Paper.Defs.S05_Def5_08_U1CompatibleYoungBlockProfile
import DictatorshipTesting.Paper.Defs.S05_Def5_24_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_25_TableauOddHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_29_AveragedHighMatchingElement
import DictatorshipTesting.Paper.S05_Lem5_13_TraceOfOneLocalTruncationOnOneYoungBlock
import DictatorshipTesting.Paper.S05_Lem5_17_BlockScalarOfTheAveragedRejection
import DictatorshipTesting.Paper.AppA_ThmA_01_YoungOrthogonalRealization
import DictatorshipTesting.Paper.AppA_ThmA_02_JucysMurphyContentSpectrum
import DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_20_EvenSpectralBridge`
- `DictatorshipTesting.Paper.S05_Lem5_21_OddSpectralBridge`
-/


/-!
Paper statement: Lemma 5.19 (`lem:regular-young-block-decomposition`)
Title in paper: Regular Young-block decomposition.

Status: assembly from external inputs.  A.1, A.2, A.3, and the Section 5
matching-average scalarity bridge input are the named representation-theoretic
inputs; this file assembles them into the dimension-parameterized spectral-block
model consumed by the active Theorem 4.8 path.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

local instance standardYoungTableauDecidableEqForRegularBlocks
    {n : Nat} {lam : YoungDiagram n} :
    DecidableEq (StandardYoungTableau lam) :=
  Classical.decEq _

/-- Pairwise orthogonal finite-coordinate components have no cross terms in
the quadratic form of an operator that is scalar on each component.

This is the elementary linear-algebra identity used by the regular Young-block
decomposition.  It deliberately takes the components and their orthogonality
as hypotheses; no representation-theoretic decomposition is hidden in the
statement. -/
theorem weightedEnergyIdentity_of_pairwiseOrthogonal_components
    {ι α : Type*} [Fintype ι] [Fintype α]
    (component : ι → α → ℝ) (theta : ι → ℝ)
    (horth : ∀ i j : ι, i ≠ j →
      (∑ x : α, component i x * component j x) = 0) :
    (∑ x : α,
        (∑ i : ι, component i x) *
          (∑ j : ι, theta j * component j x)) =
      ∑ j : ι, theta j * ∑ x : α, (component j x) ^ 2 := by
  classical
  have hcomponent (j : ι) :
      (∑ x : α, (∑ i : ι, component i x) * component j x) =
        ∑ x : α, (component j x) ^ 2 := by
    calc
      (∑ x : α, (∑ i : ι, component i x) * component j x) =
          ∑ i : ι, ∑ x : α, component i x * component j x := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ x : α, component j x * component j x := by
        rw [Fintype.sum_eq_single j]
        intro i hij
        exact horth i j hij
      _ = ∑ x : α, (component j x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
  calc
    (∑ x : α,
        (∑ i : ι, component i x) *
          (∑ j : ι, theta j * component j x)) =
        ∑ x : α, ∑ j : ι,
          theta j * ((∑ i : ι, component i x) * component j x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ j : ι, theta j *
        ∑ x : α, (∑ i : ι, component i x) * component j x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ = ∑ j : ι, theta j * ∑ x : α, (component j x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hcomponent]

/-- Normalized version of
`weightedEnergyIdentity_of_pairwiseOrthogonal_components`, matching the
uniform inner product used for functions on a finite symmetric group. -/
theorem weightedEnergyIdentity_of_pairwiseOrthogonal_components_normalized
    {ι α : Type*} [Fintype ι] [Fintype α]
    (component : ι → α → ℝ) (theta : ι → ℝ)
    (horth : ∀ i j : ι, i ≠ j →
      (∑ x : α, component i x * component j x) = 0) :
    (∑ x : α,
        (∑ i : ι, component i x) *
          (∑ j : ι, theta j * component j x)) /
          (Fintype.card α : ℝ) =
      ∑ j : ι,
        theta j *
          ((∑ x : α, (component j x) ^ 2) /
            (Fintype.card α : ℝ)) := by
  rw [weightedEnergyIdentity_of_pairwiseOrthogonal_components
    component theta horth]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The real matrix coefficient of a faithful Young action in the standard
tableau coordinate basis. -/
def youngMatrixCoefficient {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (S T : StandardYoungTableau lam) :
    Perm (Fin (n + 1)) → ℝ :=
  fun π =>
    tableauInner (tableauBasisVec S)
      (action.rep.rho π (tableauBasisVec T))

/-- A finite linear combination of all matrix coefficients of one Young
action.  No injectivity, orthogonality, or spanning assertion is built into
this definition. -/
def youngBlockSynthesis {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (coeff : StandardYoungTableau lam × StandardYoungTableau lam → ℝ) :
    Perm (Fin (n + 1)) → ℝ :=
  fun π =>
    ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
      coeff ST * youngMatrixCoefficient action ST.1 ST.2 π

/-- The concrete matrix-coefficient block of one supplied Young action.  It is
the linear span of the actual group functions `youngMatrixCoefficient` for
that shape. -/
def youngMatrixCoefficientBlock {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) :
    Submodule ℝ (Perm (Fin (n + 1)) → ℝ) :=
  Submodule.span ℝ
    (Set.range fun ST :
      StandardYoungTableau lam × StandardYoungTableau lam =>
        youngMatrixCoefficient action ST.1 ST.2)

/-- Every explicitly synthesized matrix-coefficient combination lies in the
concrete block span. -/
theorem youngBlockSynthesis_mem_youngMatrixCoefficientBlock
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (coeff : StandardYoungTableau lam × StandardYoungTableau lam → ℝ) :
    youngBlockSynthesis action coeff ∈
      youngMatrixCoefficientBlock action := by
  classical
  have hsum :
      (∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
        coeff ST • youngMatrixCoefficient action ST.1 ST.2) ∈
          youngMatrixCoefficientBlock action := by
    apply Submodule.sum_mem
    intro ST _hST
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨ST, rfl⟩
  have hsynthesis :
      youngBlockSynthesis action coeff =
        ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
          coeff ST • youngMatrixCoefficient action ST.1 ST.2 := by
    funext π
    simp [youngBlockSynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsynthesis]
  exact hsum

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
              (appA_jucysMurphyElement a) f) := by
        simpa [repOfGroupAlgebraElement] using
          congrArg (youngAveragedRankOne action T V)
            (content.rho_content a f).symm
      _ = repOfGroupAlgebraElement action.rep
          (appA_jucysMurphyElement a)
            (youngAveragedRankOne action T V f) := by
        exact youngAveragedRankOne_commutes_repOfGroupAlgebra
          action T V (appA_jucysMurphyElement a) f
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
  exact S05_Lem5_16_youngModelOperator_scalar_on_basis
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

@[simp] theorem youngMatrixCoefficient_apply
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (S T : StandardYoungTableau lam) (π : Perm (Fin (n + 1))) :
    youngMatrixCoefficient action S T π =
      action.rep.rho π (tableauBasisVec T) S := by
  simpa [youngMatrixCoefficient] using
    tableauInner_left_basis S
      (action.rep.rho π (tableauBasisVec T))

/-- With the repository's convention `(C_a F)(x) = sum_g a(g) F(xg)`, right
convolution acts on the right tableau coordinate of a Young matrix
coefficient. -/
theorem rightConvolution_youngMatrixCoefficient
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (a : GroupAlgebraElement (Perm (Fin (n + 1))))
    (S T : StandardYoungTableau lam) :
    rightConvolution a (youngMatrixCoefficient action S T) =
      fun x =>
        ∑ U : StandardYoungTableau lam,
          repOfGroupAlgebraElement action.rep a (tableauBasisVec T) U *
            youngMatrixCoefficient action S U x := by
  classical
  funext x
  let v : TableauSpace lam :=
    repOfGroupAlgebraElement action.rep a (tableauBasisVec T)
  have hv_expand :
      v = ∑ U : StandardYoungTableau lam,
        v U • tableauBasisVec U := by
    funext W
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (tableauBasis_expansion v) W
  calc
    rightConvolution a (youngMatrixCoefficient action S T) x =
        ∑ g : Perm (Fin (n + 1)),
          a g * action.rep.rho (x * g) (tableauBasisVec T) S := by
      simp only [rightConvolution, youngMatrixCoefficient_apply]
    _ = ∑ g : Perm (Fin (n + 1)),
        a g * action.rep.rho x
          (action.rep.rho g (tableauBasisVec T)) S := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [action.rep.map_mul]
    _ = action.rep.rho x v S := by
      unfold v repOfGroupAlgebraElement
      calc
        (∑ g : Perm (Fin (n + 1)),
          a g * action.rep.rho x
            (action.rep.rho g (tableauBasisVec T)) S) =
            (∑ g : Perm (Fin (n + 1)),
              a g • action.rep.rho x
                (action.rep.rho g (tableauBasisVec T))) S := by
          simp [Finset.sum_apply]
        _ = (∑ g : Perm (Fin (n + 1)),
              action.rep.rho x
                (a g • action.rep.rho g (tableauBasisVec T))) S := by
          apply congrArg (fun f : TableauSpace lam => f S)
          apply Finset.sum_congr rfl
          intro g _hg
          rw [action.rep.map_smul]
        _ = action.rep.rho x
              (∑ g : Perm (Fin (n + 1)),
                a g • action.rep.rho g (tableauBasisVec T)) S := by
          apply congrArg (fun f : TableauSpace lam => f S)
          change
            (∑ g : Perm (Fin (n + 1)),
              (action.rep.linearMap x)
                (a g • action.rep.rho g (tableauBasisVec T))) =
              (action.rep.linearMap x)
                (∑ g : Perm (Fin (n + 1)),
                  a g • action.rep.rho g (tableauBasisVec T))
          exact
            (map_sum (action.rep.linearMap x)
              (fun g : Perm (Fin (n + 1)) =>
                a g • action.rep.rho g (tableauBasisVec T))
              Finset.univ).symm
    _ = action.rep.rho x
        (∑ U : StandardYoungTableau lam,
          v U • tableauBasisVec U) S := by
      exact congrArg (fun w : TableauSpace lam => action.rep.rho x w S)
        hv_expand
    _ = ∑ U : StandardYoungTableau lam,
        v U * action.rep.rho x (tableauBasisVec U) S := by
      calc
        action.rep.rho x
            (∑ U : StandardYoungTableau lam,
              v U • tableauBasisVec U) S =
            (∑ U : StandardYoungTableau lam,
              action.rep.rho x (v U • tableauBasisVec U)) S := by
          apply congrArg (fun f : TableauSpace lam => f S)
          change
            (action.rep.linearMap x)
                (∑ U : StandardYoungTableau lam,
                  v U • tableauBasisVec U) =
              ∑ U : StandardYoungTableau lam,
                (action.rep.linearMap x) (v U • tableauBasisVec U)
          exact
            map_sum (action.rep.linearMap x)
              (fun U : StandardYoungTableau lam =>
                v U • tableauBasisVec U) Finset.univ
        _ = ∑ U : StandardYoungTableau lam,
            v U * action.rep.rho x (tableauBasisVec U) S := by
          simp [action.rep.map_smul, Finset.sum_apply]
    _ = ∑ U : StandardYoungTableau lam,
        repOfGroupAlgebraElement action.rep a (tableauBasisVec T) U *
          youngMatrixCoefficient action S U x := by
      apply Finset.sum_congr rfl
      intro U _hU
      simp only [v, youngMatrixCoefficient_apply]

/-- The actual averaged high-matching convolution is scalar on every matrix
coefficient of one supplied faithful Young action.  The scalar is the one
already proved for the represented tableau-coordinate operator. -/
theorem rightConvolution_averagedHigh_on_youngMatrixCoefficient
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 S T : StandardYoungTableau lam) :
    rightConvolution (S05_averagedHighMatchingElement (n + 1))
        (youngMatrixCoefficient action S T) =
      fun x =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_appendixA
              action content)).basisScalar T0 *
          youngMatrixCoefficient action S T x := by
  classical
  rw [rightConvolution_youngMatrixCoefficient]
  funext x
  have hscalar :=
    S05_averagedRejectionYoungOperator_scalar_from_appendixA
      action content T0 T
  change
    repOfGroupAlgebraElement action.rep
        (S05_averagedHighMatchingElement (n + 1)) (tableauBasisVec T) =
      fun U =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_appendixA
              action content)).basisScalar T0 * tableauBasisVec T U at hscalar
  rw [hscalar]
  rw [Fintype.sum_eq_single T]
  · simp
  · intro U hUT
    simp [tableauBasisVec, hUT]

/-- In even size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension.  This uses the
completed fixed-trace theorem, not the old numerical A.2 shadow. -/
theorem averagedHigh_youngBlockScalar_even
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_appendixA
          action content)).basisScalar T0 =
      hEvenTableau (m + 1) lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_13_fixedMatching_tableauTrace_even m lam action]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  have hcard :
      (Fintype.card (NearPerfectMatching (2 * (m + 1))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [Nat.mul_add]

/-- In odd size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension. -/
theorem averagedHigh_youngBlockScalar_odd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_appendixA
          action content)).basisScalar T0 =
      hOddTableau m lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_13_fixedMatching_tableauTrace_odd m lam action]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  have hcard :
      (Fintype.card (NearPerfectMatching (2 * m + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Odd concrete matrix-coefficient block scalar with its explicit
certificate value. -/
theorem rightConvolution_averagedHigh_on_youngMatrixCoefficient_odd
    (m : Nat) (lam : YoungDiagram (2 * m + 1))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 S T : StandardYoungTableau lam) :
    rightConvolution (S05_averagedHighMatchingElement (2 * m + 1))
        (youngMatrixCoefficient action S T) =
      fun x =>
        (hOddTableau m lam / tableauDim lam) *
          youngMatrixCoefficient action S T x := by
  rw [rightConvolution_averagedHigh_on_youngMatrixCoefficient
    action content T0 S T]
  rw [averagedHigh_youngBlockScalar_odd m lam action content T0]

/-- The actual averaged high-matching convolution is scalar on the entire
concrete matrix-coefficient block, not only on its named generators. -/
theorem rightConvolution_averagedHigh_scalar_on_youngMatrixCoefficientBlock
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam)
    {F : Perm (Fin (n + 1)) → ℝ}
    (hF : F ∈ youngMatrixCoefficientBlock action) :
    rightConvolution (S05_averagedHighMatchingElement (n + 1)) F =
      fun x =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_appendixA
              action content)).basisScalar T0 * F x := by
  classical
  let q := S05_averagedHighMatchingElement (n + 1)
  let c :=
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
      (S05_averagedRejectionYoungOperatorData_from_appendixA
        action content)).basisScalar T0
  refine Submodule.span_induction
    (p := fun F _ => rightConvolution q F = fun x => c * F x)
    ?mem ?zero ?add ?smul hF
  · intro Φ hΦ
    rcases hΦ with ⟨ST, rfl⟩
    exact rightConvolution_averagedHigh_on_youngMatrixCoefficient
      action content T0 ST.1 ST.2
  · funext x
    simp [rightConvolution]
  · intro F₁ F₂ _hF₁mem _hF₂mem hF₁ hF₂
    change rightConvolution q (fun x => F₁ x + F₂ x) =
      fun x => c * (F₁ x + F₂ x)
    rw [rightConvolution_add, hF₁, hF₂]
    funext x
    ring
  · intro a F _hFmem hscalar
    change rightConvolution q (fun x => a * F x) =
      fun x => c * (a * F x)
    rw [rightConvolution_smul, hscalar]
    funext x
    ring

/-- Scalarity of the averaged high-matching convolution on an explicitly
synthesized element of one Young matrix-coefficient block. -/
theorem rightConvolution_averagedHigh_youngBlockSynthesis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam)
    (coeff : StandardYoungTableau lam × StandardYoungTableau lam → ℝ) :
    rightConvolution (S05_averagedHighMatchingElement (n + 1))
        (youngBlockSynthesis action coeff) =
      fun x =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_appendixA
              action content)).basisScalar T0 *
          youngBlockSynthesis action coeff x := by
  exact rightConvolution_averagedHigh_scalar_on_youngMatrixCoefficientBlock
    action content T0
      (youngBlockSynthesis_mem_youngMatrixCoefficientBlock action coeff)

/-- Lemma 5.19 model projection: each Young-block energy is nonnegative. -/
theorem S05_Lem5_19_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Lemma 5.19 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem S05_Lem5_19_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

/-- Lemma 5.19 assembly theorem for the tableau-count even route, from the
explicit classical Appendix A ingredients.

This theorem contains no new representation-theoretic axiom of its own; it
assembles the precise A.1/A.2/A.3 component inputs and the Section 5
scalarity bridge input into the compact `SpectralBlockModelInputWithDim`
interface consumed by Section 5. -/
theorem spectralBlockModelInputWithDim_even_from_appA_inputs
    (hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (hA3 : AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement)
    (hScalarity : S05_MatchingAverageScalarityFromYoungModelStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) := by
  intro F
  rcases hA1 F with ⟨energyData⟩
  rcases hA2.1 m hm energyData with ⟨traceData⟩
  let energy : YoungBlockEnergyModel F :=
    { blockEnergy := energyData.blockEnergy
      nonneg := energyData.nonneg
      u1_identification := hA3 energyData }
  let scalar :
      MatchingAverageScalarModelWithDim
        (fun lam : YoungDiagram (2 * m) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam)
        F energy.blockEnergy :=
    { theta := traceData.theta
      scalarity := hScalarity traceData
      trace_value := traceData.trace_value }
  exact ⟨energy, ⟨scalar⟩⟩

/-- Appendix A spectral-block model input for the tableau-count even route. -/
theorem spectralBlockModelInputWithDim_even_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) :=
  spectralBlockModelInputWithDim_even_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_03_degreeOneYoungBlockIdentification
    S05_matchingAverageScalarity_from_young_model_input
    m hm

/-- Lemma 5.19 assembly theorem for the tableau-count odd route, from the
explicit classical Appendix A ingredients.

This is the odd analogue of
`spectralBlockModelInputWithDim_even_from_appendixA`, with block dimension
`tableauDim` and height `hOddTableau`. -/
theorem spectralBlockModelInputWithDim_odd_from_appA_inputs
    (hA1 : AppA_ThmA_01_YoungOrthogonalRealizationStatement)
    (hA2 : AppA_ThmA_02_JucysMurphyContentSpectrumStatement)
    (hA3 : AppA_LemA_03_DegreeOneYoungBlockIdentificationStatement)
    (hScalarity : S05_MatchingAverageScalarityFromYoungModelStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) := by
  intro F
  rcases hA1 F with ⟨energyData⟩
  rcases hA2.2 m hm energyData with ⟨traceData⟩
  let energy : YoungBlockEnergyModel F :=
    { blockEnergy := energyData.blockEnergy
      nonneg := energyData.nonneg
      u1_identification := hA3 energyData }
  let scalar :
      MatchingAverageScalarModelWithDim
        (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
        F energy.blockEnergy :=
    { theta := traceData.theta
      scalarity := hScalarity traceData
      trace_value := traceData.trace_value }
  exact ⟨energy, ⟨scalar⟩⟩

/-- Appendix A spectral-block model input for the tableau-count odd route. -/
theorem spectralBlockModelInputWithDim_odd_from_appendixA
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) :=
  spectralBlockModelInputWithDim_odd_from_appA_inputs
    AppA_ThmA_01_youngOrthogonalRealization
    AppA_ThmA_02_jucysMurphyContentSpectrum
    AppA_LemA_03_degreeOneYoungBlockIdentification
    S05_matchingAverageScalarity_from_young_model_input
    m hm

end DictatorshipTesting
