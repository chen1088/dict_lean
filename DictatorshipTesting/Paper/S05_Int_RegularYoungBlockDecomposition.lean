import DictatorshipTesting.Paper.S05_Int_SpectralBridgeRepresentationInputs
import DictatorshipTesting.Paper.S05_Int_TableauDimension
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungBlockEnergyProfile
import DictatorshipTesting.Paper.Defs.S05_IntDef_U1CompatibleYoungBlockProfile
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauOddHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_12c_AveragedHighMatchingElement
import DictatorshipTesting.Paper.S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock
import DictatorshipTesting.Paper.S05_Lem5_25_BlockScalarOfTheAveragedRejection
import DictatorshipTesting.Paper.S05_Int_YoungTableauSumOfSquares
import DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks
import DictatorshipTesting.Paper.S04_Lem4_05_PMPerpendicular
import DictatorshipTesting.Paper.S04_Cor4_07_U1Local
import Mathlib.LinearAlgebra.Basis.Basic
import DictatorshipTesting.Paper.S05_Thm5_03_YoungOrthogonalAction
import DictatorshipTesting.Paper.S05_Thm5_05_JucysMurphyContentAction
import DictatorshipTesting.Paper.S05_Lem5_12_DegreeOneYoungBlockIdentification

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.Defs.S05_Def5_06b_YoungMatrixCoefficients`
- `DictatorshipTesting.Paper.Defs.S05_Def5_06c_YoungBlockComponentsAndEnergies`
- `DictatorshipTesting.Paper.S05_Lem5_09_YoungMatrixCoefficientOrthogonality`
- `DictatorshipTesting.Paper.S05_Lem5_10_YoungTableauSumOfSquares`
- `DictatorshipTesting.Paper.S05_Lem5_11_RegularYoungBlockDecomposition`
- `DictatorshipTesting.Paper.S05_Lem5_26_GlobalWeightedMatchingIdentity`
- `DictatorshipTesting.Paper.S05_Lem5_28_EvenSpectralBridge`
- `DictatorshipTesting.Paper.S05_Lem5_29_OddSpectralBridge`
-/


/-!

Internal regular-representation machinery. This file proves the concrete
weighted matching identities and assembles those results into the
dimension-parameterized spectral-block model consumed by the active Theorem
4.10 path.
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

/-- One local projection error is the quadratic form of its concrete high
matching idempotent. -/
theorem matchingLocalProjectionError_eq_permInner_highIdempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      permInner F (S05_matchingHighIdempotent M F) := by
  have hlocal :=
    (S04_Lem4_05_PMPerpendicular F (matchingLocalProjection M F) M
      (S04_Lem4_03_PMFixesLocal F M).1).2
  rw [S05_Lem5_23_residual_eq_high_idempotent M F] at hlocal
  exact hlocal.symm

/-- The averaged matching projection error is the quadratic form of right
convolution by the actual central averaged high-matching element `q`. -/
theorem matchingMeanProjectionError_eq_inner_averagedHighConvolution
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      permInner F
        (rightConvolution (S05_averagedHighMatchingElement n) F) := by
  classical
  rw [S05_Lem5_24_matchingMeanProjectionError_eq_average]
  simp_rw [matchingLocalProjectionError_eq_permInner_highIdempotent F]
  rw [S05_averagedHighMatchingElement_rightConvolution]
  unfold permInner
  calc
    (∑ M : NearPerfectMatching n,
        (∑ π : Perm (Fin n),
          F π * S05_matchingHighIdempotent M.toOrdered F π) /
            (Fintype.card (Perm (Fin n)) : ℝ)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) =
        ((∑ M : NearPerfectMatching n,
            ∑ π : Perm (Fin n),
              F π * S05_matchingHighIdempotent M.toOrdered F π) /
            (Fintype.card (Perm (Fin n)) : ℝ)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
      congr 1
      rw [← Finset.sum_div]
    _ = ((∑ π : Perm (Fin n),
          ∑ M : NearPerfectMatching n,
            F π * S05_matchingHighIdempotent M.toOrdered F π) /
          (Fintype.card (Perm (Fin n)) : ℝ)) /
        (Fintype.card (NearPerfectMatching n) : ℝ) := by
      rw [Finset.sum_comm]
    _ = ((∑ π : Perm (Fin n),
          ∑ M : NearPerfectMatching n,
            F π * S05_matchingHighIdempotent M.toOrdered F π) /
          (Fintype.card (NearPerfectMatching n) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ) := by
      ring
    _ = (∑ π : Perm (Fin n),
          (∑ M : NearPerfectMatching n,
            F π * S05_matchingHighIdempotent M.toOrdered F π) /
              (Fintype.card (NearPerfectMatching n) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ π : Perm (Fin n),
          F π *
            ((∑ M : NearPerfectMatching n,
              S05_matchingHighIdempotent M.toOrdered F π) /
                (Fintype.card (NearPerfectMatching n) : ℝ))) /
        (Fintype.card (Perm (Fin n)) : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro π _hπ
      rw [← Finset.mul_sum]
      ring

/-- Every fixed high matching idempotent kills `U1`. -/
theorem matchingHighIdempotent_eq_zero_of_mem_U1
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> Real)
    (hF : F ∈ U1 α) :
    S05_matchingHighIdempotent M F = 0 := by
  change matchingHighConvolution M F = 0
  rw [← (S05_Int_PMConvolution M F).2, (S04_Cor4_07_U1Local M F hF).2]
  funext pi
  simp

/-- Averaging the fixed high idempotents therefore still kills `U1`. -/
theorem rightConvolution_averagedHigh_eq_zero_of_mem_U1
    {n : Nat} (F : Perm (Fin n) -> Real)
    (hF : F ∈ U1 (Fin n)) :
    rightConvolution (S05_averagedHighMatchingElement n) F = 0 := by
  classical
  rw [S05_averagedHighMatchingElement_rightConvolution]
  funext pi
  simp_rw [matchingHighIdempotent_eq_zero_of_mem_U1 _ F hF]
  simp

/-- Right convolution commutes with a finite sum of functions. -/
theorem rightConvolution_fintype_sum
    {ι G : Type*} [Fintype ι] [Fintype G] [Mul G]
    (a : GroupAlgebraElement G) (F : ι -> G -> Real) :
    rightConvolution a (∑ i : ι, F i) =
      ∑ i : ι, rightConvolution a (F i) := by
  classical
  funext x
  simp only [rightConvolution, Finset.sum_apply]
  calc
    (∑ g : G, a g * ∑ i : ι, F i (x * g)) =
        ∑ g : G, ∑ i : ι, a g * F i (x * g) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ g : G, a g * F i (x * g) := by
      rw [Finset.sum_comm]

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
  exact S05_Lem5_08_youngModelOperator_scalar_on_basis
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

/-- The faithful Lemma 5.12 subspace equality and the concrete orthogonal Young
decomposition identify squared distance to `U_1` with the energy in all other
Young blocks. -/
theorem l2DistSqToU1_eq_sum_concreteYoungBlockEnergy
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action)
    (F : Perm (Fin (n + 1)) -> Real) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks (n + 1)).sum
        (concreteYoungBlockEnergy action content F) := by
  classical
  let isU1Shape : YoungDiagram (n + 1) -> Prop :=
    fun lam => IsOneRow lam ∨ IsStandard lam
  let component := concreteYoungBlockComponent action content F
  let u1Part : Perm (Fin (n + 1)) -> Real :=
    ∑ lam : {lam : YoungDiagram (n + 1) // isU1Shape lam}, component lam.1
  let otherPart : Perm (Fin (n + 1)) -> Real :=
    ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam}, component lam.1
  have hsplit := Fintype.sum_subtype_add_sum_subtype isU1Shape component
  have hdecomp : u1Part + otherPart = F := by
    calc
      u1Part + otherPart =
          ∑ lam : YoungDiagram (n + 1), component lam := by
        simpa [u1Part, otherPart] using hsplit
      _ = F := sum_concreteYoungBlockComponent action content F
  have hu1Concrete : u1Part ∈ concreteDegreeOneYoungBlockSum action := by
    dsimp [u1Part]
    apply Submodule.sum_mem
    intro lam _hlam
    apply youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
      action lam.1 lam.2
    exact concreteYoungBlockComponent_mem action content F lam.1
  have hu1 : u1Part ∈ U1 (Fin (n + 1)) := by
    rw [hU1]
    exact hu1Concrete
  have hother_orthogonal :
      ∀ G : Perm (Fin (n + 1)) -> Real,
        G ∈ concreteDegreeOneYoungBlockSum action ->
          permInner otherPart G = 0 := by
    intro G hG
    unfold concreteDegreeOneYoungBlockSum at hG
    refine Submodule.iSup_induction
      (fun lam : YoungDiagram (n + 1) =>
        ⨆ (_h : IsOneRow lam ∨ IsStandard lam),
          youngMatrixCoefficientBlock (action lam))
      (motive := fun G => permInner otherPart G = 0) hG ?_ ?_ ?_
    · intro lam G hGlam
      refine Submodule.iSup_induction
        (fun _h : IsOneRow lam ∨ IsStandard lam =>
          youngMatrixCoefficientBlock (action lam))
        (motive := fun G => permInner otherPart G = 0) hGlam ?_ ?_ ?_
      · intro hlam G hGblock
        calc
          permInner otherPart G =
              ∑ mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu},
                permInner (component mu.1) G := by
            simpa [otherPart] using
              permInner_fintype_sum_smul_left
                (fun _mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu} =>
                  (1 : Real))
                (fun mu => component mu.1) G
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro mu _hmu
            have hshape : mu.1 ≠ lam := by
              intro heq
              apply mu.2
              dsimp [isU1Shape]
              simpa [heq] using hlam
            exact youngMatrixCoefficientBlock_orthogonal
              hshape (action mu.1) (content mu.1)
                (action lam) (content lam)
                (concreteYoungBlockComponent_mem action content F mu.1)
                hGblock
      · exact permInner_zero_right otherPart
      · intro G₁ G₂ h₁ h₂
        rw [permInner_add_right, h₁, h₂, add_zero]
    · exact permInner_zero_right otherPart
    · intro G₁ G₂ h₁ h₂
      rw [permInner_add_right, h₁, h₂, add_zero]
  have hotherNorm :
      permInner otherPart otherPart =
        (nonU1YoungBlocks (n + 1)).sum
          (concreteYoungBlockEnergy action content F) := by
    calc
      permInner otherPart otherPart =
          ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
            permInner (component lam.1) otherPart := by
        simpa [otherPart] using
          permInner_fintype_sum_smul_left
            (fun _lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam} =>
              (1 : Real))
            (fun lam => component lam.1) otherPart
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          ∑ mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu},
            permInner (component lam.1) (component mu.1) := by
        apply Finset.sum_congr rfl
        intro lam _hlam
        simpa [otherPart] using
          permInner_fintype_sum_smul_right
            (fun _mu : {mu : YoungDiagram (n + 1) // ¬ isU1Shape mu} =>
              (1 : Real))
            (fun mu => component mu.1) (component lam.1)
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          permInner (component lam.1) (component lam.1) := by
        apply Finset.sum_congr rfl
        intro lam _hlam
        rw [Fintype.sum_eq_single lam]
        intro mu hmulam
        apply concreteYoungBlockComponent_orthogonal action content F
        intro hshape
        apply hmulam
        exact Subtype.ext hshape.symm
      _ = ∑ lam : {lam : YoungDiagram (n + 1) // ¬ isU1Shape lam},
          concreteYoungBlockEnergy action content F lam.1 := by
        rfl
      _ = (nonU1YoungBlocks (n + 1)).sum
          (concreteYoungBlockEnergy action content F) := by
        symm
        apply Finset.sum_subtype
        intro lam
        simp [nonU1YoungBlocks, isU1Shape]
  have hpythagoras
      (G : Perm (Fin (n + 1)) -> Real) (hG : G ∈ U1 (Fin (n + 1))) :
      l2DistSq F G =
        (nonU1YoungBlocks (n + 1)).sum
            (concreteYoungBlockEnergy action content F) +
          l2DistSq u1Part G := by
    have hu1_sub_G : u1Part - G ∈ U1 (Fin (n + 1)) :=
      Submodule.sub_mem _ hu1 hG
    have hu1_sub_G_concrete :
        u1Part - G ∈ concreteDegreeOneYoungBlockSum action := by
      rw [← hU1]
      exact hu1_sub_G
    have horth : permInner otherPart (u1Part - G) = 0 :=
      hother_orthogonal (u1Part - G) hu1_sub_G_concrete
    have horth' : permInner (u1Part - G) otherPart = 0 := by
      rw [permInner_symm]
      exact horth
    have hdiff : F - G = otherPart + (u1Part - G) := by
      rw [← hdecomp]
      abel
    rw [l2DistSq_eq_permInner_sub, l2DistSq_eq_permInner_sub, hdiff]
    calc
      permInner (otherPart + (u1Part - G))
          (otherPart + (u1Part - G)) =
          permInner otherPart otherPart +
            permInner otherPart (u1Part - G) +
            permInner (u1Part - G) otherPart +
            permInner (u1Part - G) (u1Part - G) := by
        rw [permInner_add_left, permInner_add_right, permInner_add_right]
        ring
      _ = permInner otherPart otherPart +
          permInner (u1Part - G) (u1Part - G) := by
        rw [horth, horth']
        ring
      _ = (nonU1YoungBlocks (n + 1)).sum
            (concreteYoungBlockEnergy action content F) +
          permInner (u1Part - G) (u1Part - G) := by
        rw [hotherNorm]
  let distances : Set Real :=
    {d : Real | ∃ G : Perm (Fin (n + 1)) -> Real,
      G ∈ U1 (Fin (n + 1)) ∧ d = l2DistSq F G}
  let otherEnergy : Real :=
    (nonU1YoungBlocks (n + 1)).sum
      (concreteYoungBlockEnergy action content F)
  have hotherEnergy_mem : otherEnergy ∈ distances := by
    refine ⟨u1Part, hu1, ?_⟩
    have h := hpythagoras u1Part hu1
    simpa [otherEnergy, l2DistSq] using h.symm
  have hdistances_nonempty : distances.Nonempty :=
    ⟨otherEnergy, hotherEnergy_mem⟩
  have hdistances_bddBelow : BddBelow distances := by
    refine ⟨0, ?_⟩
    intro d hd
    rcases hd with ⟨G, _hG, rfl⟩
    unfold l2DistSq
    positivity
  have hotherEnergy_lower : ∀ d ∈ distances, otherEnergy ≤ d := by
    intro d hd
    rcases hd with ⟨G, hG, rfl⟩
    rw [hpythagoras G hG]
    dsimp [otherEnergy]
    apply le_add_of_nonneg_right
    unfold l2DistSq
    positivity
  unfold l2DistSqToU1
  change sInf distances = otherEnergy
  exact le_antisymm
    (csInf_le hdistances_bddBelow hotherEnergy_mem)
    (le_csInf hdistances_nonempty hotherEnergy_lower)

/-- Lemma Lemma 5.12 numerical consequence for the concrete Young-block energies. -/
theorem S05_Lem5_12_l2DistSqToU1_eq_nonU1_sum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) -> Real) :
    l2DistSqToU1 F =
      (S05_Lem5_12_nonU1YoungBlocks (n + 1)).sum
        (concreteYoungBlockEnergy action content F) := by
  exact l2DistSqToU1_eq_sum_concreteYoungBlockEnergy action content
    (S05_Lem5_12_U1_eq_concreteDegreeOneYoungBlockSum action) F

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
            (S05_averagedRejectionYoungOperatorData_from_section5
              action content)).basisScalar T0 *
          youngMatrixCoefficient action S T x := by
  classical
  rw [rightConvolution_youngMatrixCoefficient]
  funext x
  have hscalar :=
    S05_averagedRejectionYoungOperator_scalar_from_section5
      action content T0 T
  change
    repOfGroupAlgebraElement action.rep
        (S05_averagedHighMatchingElement (n + 1)) (tableauBasisVec T) =
      fun U =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_section5
              action content)).basisScalar T0 * tableauBasisVec T U at hscalar
  rw [hscalar]
  rw [Fintype.sum_eq_single T]
  · simp
  · intro U hUT
    simp [tableauBasisVec, hUT]

/-- In even size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension.  This uses the
completed internal fixed-trace theorem rather than the global Theorem 5.5 trace
payload. -/
theorem averagedHigh_youngBlockScalar_even
    (m : Nat) (lam : YoungDiagram (2 * (m + 1)))
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 : StandardYoungTableau lam) :
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content)).basisScalar T0 =
      hEvenTableau (m + 1) lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_22_fixedMatching_tableauTrace_even m lam action]
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
        (S05_averagedRejectionYoungOperatorData_from_section5
          action content)).basisScalar T0 =
      hOddTableau m lam / tableauDim lam := by
  have hdim : tableauDim lam ≠ 0 := tableauDim_ne_zero_of_tableau T0
  rw [S05_averagedRejectionYoungOperator_scalar_eq_trace_div_tableauDim
    action content T0 hdim]
  congr 1
  rw [S05_averagedRejectionYoungOperator_trace_eq_average_fixed]
  simp_rw [S05_Lem5_22_fixedMatching_tableauTrace_odd m lam action]
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
            (S05_averagedRejectionYoungOperatorData_from_section5
              action content)).basisScalar T0 * F x := by
  classical
  let q := S05_averagedHighMatchingElement (n + 1)
  let c :=
    (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
      (S05_averagedRejectionYoungOperatorData_from_section5
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

/-- In even rank, the averaged high-matching convolution acts on each
concrete Young-block component by the certificate scalar `h / d`. -/
theorem rightConvolution_averagedHigh_concreteYoungBlockComponent_even
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * (m + 1)),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * (m + 1)),
      JucysMurphyContentActionData (action lam))
    (hpos : ∀ lam : YoungDiagram (2 * (m + 1)), 0 < tableauDim lam)
    (F : Perm (Fin (2 * (m + 1))) → ℝ)
    (lam : YoungDiagram (2 * (m + 1))) :
    rightConvolution (S05_averagedHighMatchingElement (2 * (m + 1)))
        (concreteYoungBlockComponent action content F lam) =
      fun x =>
        (hEvenTableau (m + 1) lam / tableauDim lam) *
          concreteYoungBlockComponent action content F lam x := by
  classical
  have hdimNat : 0 < tableauDimNat lam := by
    have hdimReal : (0 : Real) < (tableauDimNat lam : Real) := by
      simpa [tableauDim] using hpos lam
    exact_mod_cast hdimReal
  rw [tableauDimNat_eq_card] at hdimNat
  let T0 : StandardYoungTableau lam :=
    Classical.choice (Fintype.card_pos_iff.mp hdimNat)
  calc
    rightConvolution (S05_averagedHighMatchingElement (2 * (m + 1)))
        (concreteYoungBlockComponent action content F lam) =
        fun x =>
          (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
              (S05_averagedRejectionYoungOperatorData_from_section5
                (action lam) (content lam))).basisScalar T0 *
            concreteYoungBlockComponent action content F lam x := by
      convert
        (rightConvolution_averagedHigh_scalar_on_youngMatrixCoefficientBlock
          (action lam) (content lam) T0
            (concreteYoungBlockComponent_mem action content F lam)) using 1 <;>
        rfl
    _ = fun x =>
        (hEvenTableau (m + 1) lam / tableauDim lam) *
          concreteYoungBlockComponent action content F lam x := by
      rw [averagedHigh_youngBlockScalar_even
        m lam (action lam) (content lam) T0]

/-- In odd rank, the averaged high-matching convolution acts on each
concrete Young-block component by the certificate scalar `h / d`. -/
theorem rightConvolution_averagedHigh_concreteYoungBlockComponent_odd
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * m + 1),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * m + 1),
      JucysMurphyContentActionData (action lam))
    (hpos : ∀ lam : YoungDiagram (2 * m + 1), 0 < tableauDim lam)
    (F : Perm (Fin (2 * m + 1)) → ℝ)
    (lam : YoungDiagram (2 * m + 1)) :
    rightConvolution (S05_averagedHighMatchingElement (2 * m + 1))
        (concreteYoungBlockComponent action content F lam) =
      fun x =>
        (hOddTableau m lam / tableauDim lam) *
          concreteYoungBlockComponent action content F lam x := by
  classical
  have hdimNat : 0 < tableauDimNat lam := by
    have hdimReal : (0 : Real) < (tableauDimNat lam : Real) := by
      simpa [tableauDim] using hpos lam
    exact_mod_cast hdimReal
  rw [tableauDimNat_eq_card] at hdimNat
  let T0 : StandardYoungTableau lam :=
    Classical.choice (Fintype.card_pos_iff.mp hdimNat)
  rw [rightConvolution_averagedHigh_scalar_on_youngMatrixCoefficientBlock
    (action lam) (content lam) T0
      (concreteYoungBlockComponent_mem action content F lam)]
  rw [averagedHigh_youngBlockScalar_odd m lam (action lam) (content lam) T0]

/-- Distinct concrete Young-block components are orthogonal for the
unnormalized finite sum as well as for `permInner`. -/
theorem concreteYoungBlockComponent_raw_orthogonal
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (F : Perm (Fin (n + 1)) → ℝ)
    {lam mu : YoungDiagram (n + 1)} (hshape : lam ≠ mu) :
    (∑ pi : Perm (Fin (n + 1)),
      concreteYoungBlockComponent action content F lam pi *
        concreteYoungBlockComponent action content F mu pi) = 0 := by
  have horth :=
    concreteYoungBlockComponent_orthogonal action content F hshape
  unfold permInner at horth
  have hcard : (Fintype.card (Perm (Fin (n + 1))) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [hcard] using horth

/-- A faithful Lemma 5.12 identification and scalar action on every concrete Young
component imply the global matching-average weighted-energy identity. -/
theorem matchingAverageScalarityInput_of_concrete_component_scalars
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (n + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action)
    (F : Perm (Fin (n + 1)) → ℝ)
    (theta : YoungDiagram (n + 1) → ℝ)
    (hscalar : ∀ lam : YoungDiagram (n + 1),
      rightConvolution (S05_averagedHighMatchingElement (n + 1))
          (concreteYoungBlockComponent action content F lam) =
        fun x => theta lam *
          concreteYoungBlockComponent action content F lam x) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F) theta := by
  classical
  let component := concreteYoungBlockComponent action content F
  have hconv :
      rightConvolution (S05_averagedHighMatchingElement (n + 1)) F =
        fun x => ∑ lam : YoungDiagram (n + 1),
          theta lam * component lam x := by
    rw [← sum_concreteYoungBlockComponent action content F]
    rw [rightConvolution_fintype_sum]
    funext x
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro lam _hlam
    rw [hscalar lam]
  have hweighted :
      permInner (∑ lam : YoungDiagram (n + 1), component lam)
          (fun x => ∑ lam : YoungDiagram (n + 1),
            theta lam * component lam x) =
        ∑ lam : YoungDiagram (n + 1),
          theta lam * concreteYoungBlockEnergy action content F lam := by
    unfold concreteYoungBlockEnergy permInner
    simpa [component, Finset.sum_apply, pow_two] using
      (weightedEnergyIdentity_of_pairwiseOrthogonal_components_normalized
        component theta fun lam mu hshape =>
          concreteYoungBlockComponent_raw_orthogonal
            action content F hshape)
  have htotal :
      matchingMeanProjectionError F =
        ∑ lam : YoungDiagram (n + 1),
          theta lam * concreteYoungBlockEnergy action content F lam := by
    calc
      matchingMeanProjectionError F =
          permInner F
            (rightConvolution
              (S05_averagedHighMatchingElement (n + 1)) F) :=
        matchingMeanProjectionError_eq_inner_averagedHighConvolution F
      _ = permInner (∑ lam : YoungDiagram (n + 1), component lam)
          (fun x => ∑ lam : YoungDiagram (n + 1),
            theta lam * component lam x) := by
        rw [sum_concreteYoungBlockComponent action content F, hconv]
      _ = ∑ lam : YoungDiagram (n + 1),
          theta lam * concreteYoungBlockEnergy action content F lam :=
        hweighted
  have hU1termZero
      (lam : YoungDiagram (n + 1))
      (hlam : IsOneRow lam ∨ IsStandard lam) :
      theta lam * concreteYoungBlockEnergy action content F lam = 0 := by
    have hcomponentU1 : component lam ∈ U1 (Fin (n + 1)) := by
      rw [hU1]
      apply youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
        action lam hlam
      exact concreteYoungBlockComponent_mem action content F lam
    have hkill :
        rightConvolution (S05_averagedHighMatchingElement (n + 1))
            (component lam) = 0 :=
      rightConvolution_averagedHigh_eq_zero_of_mem_U1
        (component lam) hcomponentU1
    have hscaled : (theta lam) • component lam = 0 := by
      funext x
      have hx := congrFun ((hscalar lam).symm.trans hkill) x
      simpa [Pi.smul_apply, smul_eq_mul] using hx
    calc
      theta lam * concreteYoungBlockEnergy action content F lam =
          permInner (component lam) ((theta lam) • component lam) := by
        rw [permInner_smul_right]
        rfl
      _ = 0 := by rw [hscaled, permInner_zero_right]
  unfold MatchingAverageScalarityInput
  rw [htotal]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro lam _hlam hnotmem
  have hU1shape : IsOneRow lam ∨ IsStandard lam := by
    have himp : ¬ IsOneRow lam → IsStandard lam := by
      simpa [nonU1YoungBlocks] using hnotmem
    by_cases hrow : IsOneRow lam
    · exact Or.inl hrow
    · exact Or.inr (himp hrow)
  exact hU1termZero lam hU1shape

/-- Concrete global weighted matching identity in positive even rank. -/
theorem S05_matchingAverageScalarity_concrete_even
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * (m + 1)),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * (m + 1)),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * (m + 1))) =
      concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * (m + 1)), 0 < tableauDim lam)
    (F : Perm (Fin (2 * (m + 1))) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hEvenTableau (m + 1) lam / tableauDim lam) := by
  apply matchingAverageScalarityInput_of_concrete_component_scalars
    action content hU1 F
  intro lam
  exact rightConvolution_averagedHigh_concreteYoungBlockComponent_even
    m action content hpos F lam

/-- Concrete global weighted matching identity in odd rank. -/
theorem S05_matchingAverageScalarity_concrete_odd
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * m + 1),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * m + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * m + 1)) =
      concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * m + 1), 0 < tableauDim lam)
    (F : Perm (Fin (2 * m + 1)) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hOddTableau m lam / tableauDim lam) := by
  apply matchingAverageScalarityInput_of_concrete_component_scalars
    action content hU1 F
  intro lam
  exact rightConvolution_averagedHigh_concreteYoungBlockComponent_odd
    m action content hpos F lam

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
            (S05_averagedRejectionYoungOperatorData_from_section5
              action content)).basisScalar T0 *
          youngBlockSynthesis action coeff x := by
  exact rightConvolution_averagedHigh_scalar_on_youngMatrixCoefficientBlock
    action content T0
      (youngBlockSynthesis_mem_youngMatrixCoefficientBlock action coeff)

/-- Lemma 5.11 model projection: each Young-block energy is nonnegative. -/
theorem S05_Lem5_11_blockEnergy_nonnegative {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F)
    (lam : YoungDiagram n) :
    0 ≤ energy.blockEnergy lam :=
  energy.nonneg lam

/-- Lemma 5.11 model projection: the distance to `U_1` is the sum of all
non-`U_1` Young-block energies. -/
theorem S05_Lem5_11_u1_identification {n : Nat}
    {F : Perm (Fin n) → ℝ}
    (energy : YoungBlockEnergyModel F) :
    l2DistSqToU1 F =
      (nonU1YoungBlocks n).sum energy.blockEnergy :=
  energy.u1_identification

/-- Lemma 5.11 assembly theorem for the tableau-count even route, from the
explicit classical Section 5 ingredients.

This theorem contains no new representation-theoretic axiom of its own; it
assembles the precise Theorems 5.3 and 5.5 component inputs, the internally proved Lemma 5.12
equality, and the concrete weighted matching identity into the compact
`SpectralBlockModelInputWithDim` interface consumed by Section 5. -/
theorem spectralBlockModelInputWithDim_even_from_s05_inputs
    (hA1 : S05_Thm5_03_YoungOrthogonalActionStatement)
    (hA2 : S05_Thm5_05_JucysMurphyContentActionStatement)
    (hA3 : S05_Lem5_12_DegreeOneYoungBlockIdentificationStatement)
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) := by
  cases m with
  | zero => omega
  | succ m =>
      intro F
      let action :
          ∀ lam : YoungDiagram (2 * Nat.succ m),
            YoungOrthogonalActionData lam :=
        fun lam => Classical.choice (hA1 lam)
      let content :
          ∀ lam : YoungDiagram (2 * Nat.succ m),
            JucysMurphyContentActionData (action lam) :=
        fun lam => Classical.choice (hA2 (action lam))
      let energy : YoungBlockEnergyModel F :=
        { blockEnergy := concreteYoungBlockEnergy action content F
          nonneg := concreteYoungBlockEnergy_nonnegative action content F
          u1_identification :=
            l2DistSqToU1_eq_sum_concreteYoungBlockEnergy action content
              (hA3 action) F }
      let scalar :
          MatchingAverageScalarModelWithDim
            (fun lam : YoungDiagram (2 * Nat.succ m) => tableauDim lam)
            (fun lam : YoungDiagram (2 * Nat.succ m) =>
              hEvenTableau (Nat.succ m) lam)
            F energy.blockEnergy :=
        { theta := fun lam =>
            hEvenTableau (Nat.succ m) lam / tableauDim lam
          scalarity :=
            S05_matchingAverageScalarity_concrete_even
              m action content (hA3 action)
                (fun lam => tableauDim_pos_all lam) F
          trace_value := fun lam =>
            ⟨tableauDim_pos_all lam, rfl⟩ }
      exact ⟨energy, ⟨scalar⟩⟩

/-- Section 5 spectral-block model input for the tableau-count even route. -/
theorem spectralBlockModelInputWithDim_even_from_section5
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m) => hEvenTableau m lam) :=
  spectralBlockModelInputWithDim_even_from_s05_inputs
    S05_Thm5_03_youngOrthogonalAction
    S05_Thm5_05_jucysMurphyContentAction
    S05_Lem5_12_degreeOneYoungBlockIdentification
    m hm

/-- Lemma 5.11 assembly theorem for the tableau-count odd route, from the
explicit classical Section 5 ingredients.

This is the odd analogue of
`spectralBlockModelInputWithDim_even_from_section5`, with block dimension
`tableauDim` and height `hOddTableau`. -/
theorem spectralBlockModelInputWithDim_odd_from_s05_inputs
    (hA1 : S05_Thm5_03_YoungOrthogonalActionStatement)
    (hA2 : S05_Thm5_05_JucysMurphyContentActionStatement)
    (hA3 : S05_Lem5_12_DegreeOneYoungBlockIdentificationStatement)
    (m : Nat) (_hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) := by
  intro F
  let action :
      ∀ lam : YoungDiagram (2 * m + 1), YoungOrthogonalActionData lam :=
    fun lam => Classical.choice (hA1 lam)
  let content :
      ∀ lam : YoungDiagram (2 * m + 1),
        JucysMurphyContentActionData (action lam) :=
    fun lam => Classical.choice (hA2 (action lam))
  let energy : YoungBlockEnergyModel F :=
    { blockEnergy := concreteYoungBlockEnergy action content F
      nonneg := concreteYoungBlockEnergy_nonnegative action content F
      u1_identification :=
        l2DistSqToU1_eq_sum_concreteYoungBlockEnergy action content
          (hA3 action) F }
  let scalar :
      MatchingAverageScalarModelWithDim
        (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
        (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam)
        F energy.blockEnergy :=
    { theta := fun lam => hOddTableau m lam / tableauDim lam
      scalarity :=
        S05_matchingAverageScalarity_concrete_odd
          m action content (hA3 action)
            (fun lam => tableauDim_pos_all lam) F
      trace_value := fun lam =>
        ⟨tableauDim_pos_all lam, rfl⟩ }
  exact ⟨energy, ⟨scalar⟩⟩

/-- Section 5 spectral-block model input for the tableau-count odd route. -/
theorem spectralBlockModelInputWithDim_odd_from_section5
    (m : Nat) (hm : 2 <= m) :
    SpectralBlockModelInputWithDim
      (fun lam : YoungDiagram (2 * m + 1) => tableauDim lam)
      (fun lam : YoungDiagram (2 * m + 1) => hOddTableau m lam) :=
  spectralBlockModelInputWithDim_odd_from_s05_inputs
    S05_Thm5_03_youngOrthogonalAction
    S05_Thm5_05_jucysMurphyContentAction
    S05_Lem5_12_degreeOneYoungBlockIdentification
    m hm

end DictatorshipTesting
