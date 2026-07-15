import DictatorshipTesting.Paper.S05_Lem5_14_MatchingFourierProjections
import DictatorshipTesting.Paper.S04_Prop4_02_CosetwiseDescriptionOfPM
import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents
import DictatorshipTesting.Paper.S05_Lem5_15_TraceOfOneLocalTruncationOnOneYoungBlock
import DictatorshipTesting.Paper.S05_Lem5_05_YoungBasisScalarCommutant
import DictatorshipTesting.Paper.S05_Int_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.Defs.S05_IntDef_YoungBlockEnergyProfile
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauOddHeight
import DictatorshipTesting.Paper.Defs.S05_Def5_12c_AveragedHighMatchingElement
import DictatorshipTesting.Paper.S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne
import DictatorshipTesting.Paper.S05_Lem5_06_YoungMatrixCoefficientOrthogonality
import DictatorshipTesting.Paper.S05_Lem5_08_RegularYoungBlockDecomposition
import DictatorshipTesting.Paper.S05_Lem5_09_DegreeOneYoungBlockIdentification

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S04_Thm4_04_MatchingGap`
-/

/-!
# Proposition 5.16: Averaged rejection on Young blocks

Centrality, the block-scalar calculation, and the resulting weighted block
identity are collected in this paper-facing module.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Proposition 5.16 finite-average component: the local rejection error is the
square distance from `F` to its matching-local projection. -/
theorem S05_Prop5_16_matchingLocalProjectionError_eq_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq F (matchingLocalProjection M F) := by
  rfl

/-- Proposition 5.16 finite-average component: the local rejection error is the
square norm of the high matching idempotent. -/
theorem S05_Prop5_16_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      l2DistSq (S05_matchingHighIdempotent M F) (fun _ => 0) := by
  unfold matchingLocalProjectionError l2DistSq
  congr 1
  apply Finset.sum_congr rfl
  intro π _hπ
  have hres := congrFun (S05_Lem5_14_residual_eq_high_idempotent M F) π
  rw [← hres]
  ring

/-- Proposition 5.16 finite-average component: the averaged rejection is the uniform
finite average of local projection errors over near-perfect matchings.  This is
the concrete quantity whose future operator-level refinement is centrality. -/
theorem S05_Prop5_16_matchingMeanProjectionError_eq_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        matchingLocalProjectionError F M.toOrdered) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rfl

/-- Proposition 5.16 finite-average component: the averaged rejection is the uniform
average of the squared high-idempotent norms. -/
theorem S05_Prop5_16_matchingMeanProjectionError_eq_high_idempotent_average
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      (∑ M : NearPerfectMatching n,
        l2DistSq (S05_matchingHighIdempotent M.toOrdered F) (fun _ => 0)) /
          (Fintype.card (NearPerfectMatching n) : ℝ) := by
  rw [S05_Prop5_16_matchingMeanProjectionError_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro M _hM
  exact S05_Prop5_16_matchingLocalProjectionError_eq_high_idempotent_l2DistSq
    F M.toOrdered


/-- One local projection error is the quadratic form of its concrete high
matching idempotent. -/
theorem matchingLocalProjectionError_eq_permInner_highIdempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) :
    matchingLocalProjectionError F M =
      permInner F (S05_matchingHighIdempotent M F) := by
  have hlocal :=
    (S04_Prop4_02_perpendicular F (matchingLocalProjection M F) M
      (S04_Prop4_02_fixedSpace F M).1).2
  rw [S05_Lem5_14_residual_eq_high_idempotent M F] at hlocal
  exact hlocal.symm

/-- If a scalar operator on a block of dimension `d^2` has trace `d * h`, then
its scalar is `h / d`.  This is the trace-divided-by-dimension calculation in
the centralization lemma. -/
theorem scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  have hd2 : d ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hd
  calc
    theta = (d ^ (2 : ℕ) * theta) / d ^ (2 : ℕ) := by
      field_simp [hd2]
    _ = (d * h) / d ^ (2 : ℕ) := by
      rw [htrace]
    _ = h / d := by
      field_simp [hd]

/-- Even Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem even_youngBlockScalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact scalar_eq_trace_div_dimension
    (youngDim lam) (hEven m lam) theta hdim htrace

/-- Odd Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem odd_youngBlockScalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact scalar_eq_trace_div_dimension
    (youngDim lam) (hOdd m lam) theta hdim htrace

/-- Centralization scalar algebra: if a scalar operator on a block of dimension
`d^2` has trace `d * h`, then the scalar is `h / d`. -/
theorem centralizationBridge_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact scalar_eq_trace_div_dimension d h theta hd htrace

/-- Even Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem centralizationBridge_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact even_youngBlockScalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Odd Young-block scalar formula, assuming scalarity and the trace
identity. -/
theorem centralizationBridge_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact odd_youngBlockScalar_eq_hOdd_div_dim m lam theta hdim htrace

/-- Proposition 5.16 paper-numbered scalar algebra: trace divided by dimension. -/
theorem S05_Prop5_16_scalar_eq_trace_div_dimension
    (d h theta : ℝ) (hd : d ≠ 0)
    (htrace : d ^ (2 : ℕ) * theta = d * h) :
    theta = h / d := by
  exact centralizationBridge_scalar_eq_trace_div_dimension d h theta hd htrace

/-- Proposition 5.16 paper-numbered even scalar formula. -/
theorem S05_Prop5_16_even_scalar_eq_hEven_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hEven m lam) :
    theta = hEven m lam / youngDim lam := by
  exact centralizationBridge_even_scalar_eq_hEven_div_dim m lam theta hdim htrace

/-- Proposition 5.16 paper-numbered odd scalar formula. -/
theorem S05_Prop5_16_odd_scalar_eq_hOdd_div_dim
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) (theta : ℝ)
    (hdim : youngDim lam ≠ 0)
    (htrace :
      (youngDim lam) ^ (2 : ℕ) * theta =
        youngDim lam * hOdd m lam) :
    theta = hOdd m lam / youngDim lam := by
  exact centralizationBridge_odd_scalar_eq_hOdd_div_dim m lam theta hdim htrace


/-- In even size, the scalar of the concrete averaged Young operator is the
tableau-count certificate divided by the tableau dimension.  This uses the
completed internal fixed-trace theorem rather than the global Theorem 5.3 trace
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
  simp_rw [S05_Lem5_15_fixedMatching_tableauTrace_even m lam action]
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
  simp_rw [S05_Lem5_15_fixedMatching_tableauTrace_odd m lam action]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  have hcard :
      (Fintype.card (NearPerfectMatching (2 * m + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

local instance standardYoungTableauDecidableEqForWeightedIdentity
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

/-- The averaged matching projection error is the quadratic form of right
convolution by the actual central averaged high-matching element `q`. -/
theorem matchingMeanProjectionError_eq_inner_averagedHighConvolution
    {n : Nat} (F : Perm (Fin n) → ℝ) :
    matchingMeanProjectionError F =
      permInner F
        (rightConvolution (S05_averagedHighMatchingElement n) F) := by
  classical
  rw [S05_Prop5_16_matchingMeanProjectionError_eq_average]
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
  rw [← (S05_Int_PMConvolution M F).2, (S04_Lem4_03_GlobalDegreeOneIsLocallyDegreeOne M F hF).2]
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

/-- A faithful Lemma 5.9 identification and scalar action on every concrete Young
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


/-- Spectral-block model assembly for the tableau-count even route, from the
explicit classical Section 5 ingredients.

This theorem contains no new representation-theoretic axiom of its own; it
assembles the precise Theorems 5.2 and 5.3 component inputs, the internally proved Lemma 5.9
equality, and the concrete weighted matching identity into the compact
`SpectralBlockModelInputWithDim` interface consumed by Section 5. -/
theorem spectralBlockModelInputWithDim_even_from_s05_inputs
    (hA1 : ∀ {n : Nat} (lam : YoungDiagram (n + 1)),
      Nonempty (YoungOrthogonalActionData lam))
    (hA2 : ∀ {n : Nat} {lam : YoungDiagram (n + 1)}
      (action : YoungOrthogonalActionData lam),
      Nonempty (JucysMurphyContentActionData action))
    (hA3 : ∀ {n : Nat}
      (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam),
      U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action)
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
    S05_Thm5_02_youngOrthogonalAction
    S05_Thm5_03_jucysMurphyContentAction
    S05_Lem5_09_degreeOneYoungBlockIdentification
    m hm

/-- Spectral-block model assembly for the tableau-count odd route, from the
explicit classical Section 5 ingredients.

This is the odd analogue of
`spectralBlockModelInputWithDim_even_from_section5`, with block dimension
`tableauDim` and height `hOddTableau`. -/
theorem spectralBlockModelInputWithDim_odd_from_s05_inputs
    (hA1 : ∀ {n : Nat} (lam : YoungDiagram (n + 1)),
      Nonempty (YoungOrthogonalActionData lam))
    (hA2 : ∀ {n : Nat} {lam : YoungDiagram (n + 1)}
      (action : YoungOrthogonalActionData lam),
      Nonempty (JucysMurphyContentActionData action))
    (hA3 : ∀ {n : Nat}
      (action : ∀ lam : YoungDiagram (n + 1), YoungOrthogonalActionData lam),
      U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action)
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
    S05_Thm5_02_youngOrthogonalAction
    S05_Thm5_03_jucysMurphyContentAction
    S05_Lem5_09_degreeOneYoungBlockIdentification
    m hm



theorem S05_Prop5_16_global_weighted_matching_identity_even
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * (m + 1)),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * (m + 1)),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * (m + 1))) = concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * (m + 1)), 0 < tableauDim lam)
    (F : Perm (Fin (2 * (m + 1))) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hEvenTableau (m + 1) lam / tableauDim lam) :=
  S05_matchingAverageScalarity_concrete_even m action content hU1 hpos F

theorem S05_Prop5_16_global_weighted_matching_identity_odd
    (m : Nat)
    (action : ∀ lam : YoungDiagram (2 * m + 1),
      YoungOrthogonalActionData lam)
    (content : ∀ lam : YoungDiagram (2 * m + 1),
      JucysMurphyContentActionData (action lam))
    (hU1 : U1 (Fin (2 * m + 1)) = concreteDegreeOneYoungBlockSum action)
    (hpos : ∀ lam : YoungDiagram (2 * m + 1), 0 < tableauDim lam)
    (F : Perm (Fin (2 * m + 1)) → ℝ) :
    MatchingAverageScalarityInput F
      (concreteYoungBlockEnergy action content F)
      (fun lam => hOddTableau m lam / tableauDim lam) :=
  S05_matchingAverageScalarity_concrete_odd m action content hU1 hpos F

end DictatorshipTesting
