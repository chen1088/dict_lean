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
