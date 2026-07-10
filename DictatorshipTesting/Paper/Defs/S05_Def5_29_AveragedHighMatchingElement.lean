import DictatorshipTesting.Paper.Defs.S05_Def5_22_MatchingIdempotents
import DictatorshipTesting.Paper.Defs.S05_Def5_28_GroupAlgebraAction

/-
Direct reverse imports:
- `DictatorshipTesting`
-/

/-!
Paper statement: Definition 5.29 (`def:averaged-high-matching-element`)
Title in paper: Averaged high-matching group-algebra element.

Status: definition plus proved covariance and centrality.  The coefficient
function is obtained by pushing the high-character Fourier kernel of each
matching cube into the symmetric group and then averaging over all ordered
near-perfect matchings.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Relabel every endpoint of an ordered matching by a permutation. -/
def OrderedMatching.relabel {α : Type*} [DecidableEq α]
    (σ : Perm α) (M : OrderedMatching α) : OrderedMatching α where
  edgeCount := M.edgeCount
  left r := σ (M.left r)
  right r := σ (M.right r)
  left_ne_right r := by
    intro h
    exact M.left_ne_right r (σ.injective h)
  edges_disjoint := by
    intro r s hrs
    rcases M.edges_disjoint hrs with ⟨hll, hlr, hrl, hrr⟩
    exact ⟨fun h => hll (σ.injective h),
      fun h => hlr (σ.injective h),
      fun h => hrl (σ.injective h),
      fun h => hrr (σ.injective h)⟩

/-- Relabel every endpoint of a near-perfect matching by a permutation. -/
def NearPerfectMatching.relabel {n : Nat}
    (σ : Perm (Fin n)) (M : NearPerfectMatching n) : NearPerfectMatching n where
  left r := σ (M.left r)
  right r := σ (M.right r)
  left_ne_right r := by
    intro h
    exact M.left_ne_right r (σ.injective h)
  edges_disjoint := by
    intro r s hrs
    rcases M.edges_disjoint hrs with ⟨hll, hlr, hrl, hrr⟩
    exact ⟨fun h => hll (σ.injective h),
      fun h => hlr (σ.injective h),
      fun h => hrl (σ.injective h),
      fun h => hrr (σ.injective h)⟩

/-- Relabeling by a fixed permutation is a bijection of the finite matching
family. -/
def nearPerfectMatchingRelabelEquiv {n : Nat} (σ : Perm (Fin n)) :
    NearPerfectMatching n ≃ NearPerfectMatching n where
  toFun := NearPerfectMatching.relabel σ
  invFun := NearPerfectMatching.relabel σ⁻¹
  left_inv := by
    intro M
    cases M
    simp [NearPerfectMatching.relabel]
  right_inv := by
    intro M
    cases M
    simp [NearPerfectMatching.relabel]

/-- Relabeling commutes with the conversion to an ordered matching. -/
theorem nearPerfectMatching_toOrdered_relabel {n : Nat}
    (σ : Perm (Fin n)) (M : NearPerfectMatching n) :
    (M.relabel σ).toOrdered = M.toOrdered.relabel σ := by
  rfl

/-- Conjugating one matching transposition relabels its two endpoints. -/
theorem orderedMatching_edgeSwap_relabel {α : Type*} [DecidableEq α]
    (σ : Perm α) (M : OrderedMatching α) (r : Fin M.edgeCount) :
    (M.relabel σ).edgeSwap r = σ * M.edgeSwap r * σ⁻¹ := by
  ext a
  change Equiv.swap (σ (M.left r)) (σ (M.right r)) a =
    σ (Equiv.swap (M.left r) (M.right r) (σ⁻¹ a))
  by_cases hal : a = σ (M.left r)
  · subst a
    simp
  by_cases har : a = σ (M.right r)
  · subst a
    simp
  have hsymm_left : σ⁻¹ a ≠ M.left r := by
    intro h
    apply hal
    simpa using congrArg σ h
  have hsymm_right : σ⁻¹ a ≠ M.right r := by
    intro h
    apply har
    simpa using congrArg σ h
  rw [Equiv.swap_apply_of_ne_of_ne hal har]
  rw [Equiv.swap_apply_of_ne_of_ne hsymm_left hsymm_right]
  simp

/-- Relabeling conjugates each optional matching transposition. -/
theorem orderedMatching_edgePerm_relabel {α : Type*} [DecidableEq α]
    (σ : Perm α) (M : OrderedMatching α) (x : Cube M.edgeCount)
    (r : Fin M.edgeCount) :
    (M.relabel σ).edgePerm x r = σ * M.edgePerm x r * σ⁻¹ := by
  by_cases hx : x r
  · simp [OrderedMatching.edgePerm, hx, orderedMatching_edgeSwap_relabel]
  · simp [OrderedMatching.edgePerm, hx]

/-- A product of conjugated permutations is the conjugate of their product. -/
theorem list_perm_prod_conjugate {α : Type*}
    (σ : Perm α) (l : List (Perm α)) :
    (l.map fun τ => σ * τ * σ⁻¹).prod = σ * l.prod * σ⁻¹ := by
  induction l with
  | nil => simp
  | cons τ l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      group

/-- Relabeling a matching conjugates every element of its matching cube. -/
theorem orderedMatching_tau_relabel {α : Type*} [DecidableEq α]
    (σ : Perm α) (M : OrderedMatching α) (x : Cube M.edgeCount) :
    (M.relabel σ).tau x = σ * M.tau x * σ⁻¹ := by
  unfold OrderedMatching.tau
  change
    (List.ofFn fun r : Fin M.edgeCount => (M.relabel σ).edgePerm x r).prod =
      σ * (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).prod * σ⁻¹
  calc
    (List.ofFn fun r : Fin M.edgeCount => (M.relabel σ).edgePerm x r).prod =
        (List.ofFn fun r : Fin M.edgeCount =>
          σ * M.edgePerm x r * σ⁻¹).prod := by
      congr 1
      exact congrArg List.ofFn (funext fun r =>
        orderedMatching_edgePerm_relabel σ M x r)
    _ = ((List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).map
          (fun τ => σ * τ * σ⁻¹)).prod := by
      exact congrArg List.prod
        (List.ofFn_comp' (fun r : Fin M.edgeCount => M.edgePerm x r)
          (fun τ => σ * τ * σ⁻¹))
    _ = σ * (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).prod * σ⁻¹ :=
      list_perm_prod_conjugate σ _

/-- The high-character Fourier kernel on one matching cube. -/
def S05_matchingHighKernel {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) : Real :=
  (∑ S ∈ S05_matchingHighCharacterSet M,
      cubeChar S x * cubeChar S (cubeZero M.edgeCount)) /
    (Fintype.card (Cube M.edgeCount) : Real)

/-- The coefficient function of the high matching idempotent for one fixed
matching.  The sum over preimages avoids requiring a separate injectivity
lemma for `M.tau`. -/
def S05_fixedMatchingHighElement {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) : GroupAlgebraElement (Perm α) :=
  fun g => ∑ x : Cube M.edgeCount,
    if M.tau x = g then S05_matchingHighKernel M x else 0

/-- Right convolution by the fixed-matching coefficient function is exactly
the existing high matching idempotent. -/
theorem S05_fixedMatchingHighElement_rightConvolution
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α -> Real) :
    rightConvolution (S05_fixedMatchingHighElement M) F =
      S05_matchingHighIdempotent M F := by
  classical
  funext π
  change
    (∑ g : Perm α,
      (∑ x : Cube M.edgeCount,
        if M.tau x = g then S05_matchingHighKernel M x else 0) *
          F (π * g)) =
      ∑ S ∈ S05_matchingHighCharacterSet M,
        cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
          cubeChar S (cubeZero M.edgeCount)
  calc
    (∑ g : Perm α,
      (∑ x : Cube M.edgeCount,
        if M.tau x = g then S05_matchingHighKernel M x else 0) *
          F (π * g)) =
        ∑ g : Perm α, ∑ x : Cube M.edgeCount,
          (if M.tau x = g then S05_matchingHighKernel M x else 0) *
            F (π * g) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_mul]
    _ = ∑ x : Cube M.edgeCount, ∑ g : Perm α,
          (if M.tau x = g then S05_matchingHighKernel M x else 0) *
            F (π * g) := by
      rw [Finset.sum_comm]
    _ = ∑ x : Cube M.edgeCount,
          S05_matchingHighKernel M x * F (π * M.tau x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp
    _ = ∑ x : Cube M.edgeCount,
        ∑ S ∈ S05_matchingHighCharacterSet M,
          (F (π * M.tau x) * cubeChar S x) /
              (Fintype.card (Cube M.edgeCount) : Real) *
            cubeChar S (cubeZero M.edgeCount) := by
      apply Finset.sum_congr rfl
      intro x _hx
      unfold S05_matchingHighKernel
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _hS
      ring
    _ = ∑ S ∈ S05_matchingHighCharacterSet M,
        ∑ x : Cube M.edgeCount,
          (F (π * M.tau x) * cubeChar S x) /
              (Fintype.card (Cube M.edgeCount) : Real) *
            cubeChar S (cubeZero M.edgeCount) := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ S05_matchingHighCharacterSet M,
        cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
          cubeChar S (cubeZero M.edgeCount) := by
      apply Finset.sum_congr rfl
      intro S _hS
      unfold cubeFourierCoeff cubeExpectation
      rw [Finset.sum_div, Finset.sum_mul]

/-- Relabeling a fixed matching conjugates its high group-algebra element. -/
theorem S05_fixedMatchingHighElement_relabel
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (M : OrderedMatching α) (g : Perm α) :
    S05_fixedMatchingHighElement (M.relabel σ) (σ * g * σ⁻¹) =
      S05_fixedMatchingHighElement M g := by
  classical
  unfold S05_fixedMatchingHighElement
  apply Finset.sum_congr rfl
  intro x _hx
  rw [orderedMatching_tau_relabel]
  have hkernel :
      S05_matchingHighKernel (M.relabel σ) x =
        S05_matchingHighKernel M x := by
    rfl
  have hcond :
      σ * M.tau x * σ⁻¹ = σ * g * σ⁻¹ ↔ M.tau x = g := by
    constructor
    · intro h
      have h' := congrArg (fun τ => σ⁻¹ * τ * σ) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h]
  by_cases h : M.tau x = g
  · rw [if_pos (hcond.mpr h), if_pos h, hkernel]
  · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]

/-- The actual averaged high-matching element
`q = E_M q_M` on the symmetric group. -/
def S05_averagedHighMatchingElement (n : Nat) :
    GroupAlgebraElement (Perm (Fin n)) :=
  fun g =>
    (∑ M : NearPerfectMatching n,
      S05_fixedMatchingHighElement M.toOrdered g) /
        (Fintype.card (NearPerfectMatching n) : Real)

/-- Right convolution by the averaged coefficient function is the uniform
average of the existing fixed-matching high idempotents. -/
theorem S05_averagedHighMatchingElement_rightConvolution
    {n : Nat} (F : Perm (Fin n) -> Real) :
    rightConvolution (S05_averagedHighMatchingElement n) F =
      fun π =>
        (∑ M : NearPerfectMatching n,
          S05_matchingHighIdempotent M.toOrdered F π) /
            (Fintype.card (NearPerfectMatching n) : Real) := by
  classical
  funext π
  unfold rightConvolution S05_averagedHighMatchingElement
  calc
    (∑ g : Perm (Fin n),
      ((∑ M : NearPerfectMatching n,
        S05_fixedMatchingHighElement M.toOrdered g) /
          (Fintype.card (NearPerfectMatching n) : Real)) * F (π * g)) =
        (∑ g : Perm (Fin n),
          (∑ M : NearPerfectMatching n,
            S05_fixedMatchingHighElement M.toOrdered g) * F (π * g)) /
              (Fintype.card (NearPerfectMatching n) : Real) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = (∑ g : Perm (Fin n), ∑ M : NearPerfectMatching n,
          S05_fixedMatchingHighElement M.toOrdered g * F (π * g)) /
            (Fintype.card (NearPerfectMatching n) : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_mul]
    _ = (∑ M : NearPerfectMatching n, ∑ g : Perm (Fin n),
          S05_fixedMatchingHighElement M.toOrdered g * F (π * g)) /
            (Fintype.card (NearPerfectMatching n) : Real) := by
      rw [Finset.sum_comm]
    _ = (∑ M : NearPerfectMatching n,
          S05_matchingHighIdempotent M.toOrdered F π) /
            (Fintype.card (NearPerfectMatching n) : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro M _hM
      exact congrFun
        (S05_fixedMatchingHighElement_rightConvolution M.toOrdered F) π

/-- The averaged high-matching coefficient function is invariant under
conjugation. -/
theorem S05_averagedHighMatchingElement_conj
    {n : Nat} (σ g : Perm (Fin n)) :
    S05_averagedHighMatchingElement n (σ * g * σ⁻¹) =
      S05_averagedHighMatchingElement n g := by
  classical
  unfold S05_averagedHighMatchingElement
  congr 1
  calc
    (∑ M : NearPerfectMatching n,
        S05_fixedMatchingHighElement M.toOrdered (σ * g * σ⁻¹)) =
        ∑ M : NearPerfectMatching n,
          S05_fixedMatchingHighElement
            ((nearPerfectMatchingRelabelEquiv σ) M).toOrdered
            (σ * g * σ⁻¹) := by
      exact (Equiv.sum_comp (nearPerfectMatchingRelabelEquiv σ)
        (fun M : NearPerfectMatching n =>
          S05_fixedMatchingHighElement M.toOrdered (σ * g * σ⁻¹))).symm
    _ = ∑ M : NearPerfectMatching n,
        S05_fixedMatchingHighElement M.toOrdered g := by
      apply Finset.sum_congr rfl
      intro M _hM
      change S05_fixedMatchingHighElement (M.relabel σ).toOrdered
          (σ * g * σ⁻¹) =
        S05_fixedMatchingHighElement M.toOrdered g
      rw [nearPerfectMatching_toOrdered_relabel]
      exact S05_fixedMatchingHighElement_relabel σ M.toOrdered g

/-- The averaged high-matching element is coefficient-central. -/
theorem S05_averagedHighMatchingElement_central (n : Nat) :
    (S05_averagedHighMatchingElement n).IsCentralByCoefficients := by
  intro σ g
  have h := S05_averagedHighMatchingElement_conj
    (n := n) σ⁻¹ (g * σ⁻¹)
  simpa [GroupAlgebraElement.CommutesWithGroupElement, mul_assoc] using h.symm

/-- The genuine averaged high-matching element acts on a supplied Young
representation model. -/
def S05_averagedRejectionYoungOperator {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam) :
    TableauSpace lam -> TableauSpace lam :=
  averagedRejectionYoungOperatorOfGroupAlgebra young
    (S05_averagedHighMatchingElement (n + 1))

/-- The actual averaged high-matching operator supplies the one-block
commutation interface for every supplied Young representation model. -/
def S05_averagedRejectionYoungOperatorData_actual {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam) :
    AveragedRejectionYoungOperatorData lam :=
  averagedRejectionYoungOperatorData_of_centralGroupAlgebraElement young
    (S05_averagedHighMatchingElement (n + 1))
    (S05_averagedHighMatchingElement_central (n + 1))

/-- The genuine averaged high-matching Young operator commutes with every
adjacent Young operator. -/
theorem S05_averagedRejectionYoungOperator_commutes_adjacent
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (a : Fin n) (f : TableauSpace lam) :
    S05_averagedRejectionYoungOperator young (youngAdjacentOperator a f) =
      youngAdjacentOperator a (S05_averagedRejectionYoungOperator young f) := by
  exact (S05_averagedRejectionYoungOperatorData_actual young).commutes_adjacent a f

/-- The genuine averaged high-matching Young operator commutes with every
diagonal content operator. -/
theorem S05_averagedRejectionYoungOperator_commutes_content
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam)
    (a : Fin (n + 1)) (f : TableauSpace lam) :
    S05_averagedRejectionYoungOperator young
        (jucysMurphyDiagonalOperator a f) =
      jucysMurphyDiagonalOperator a
        (S05_averagedRejectionYoungOperator young f) := by
  exact (S05_averagedRejectionYoungOperatorData_actual young).commutes_content a f

/-- On any supplied Young representation model, the genuine averaged
high-matching operator is scalar on the tableau basis. -/
theorem S05_averagedRejectionYoungOperator_scalar_on_basis
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (hconn : External.AppendixA.StandardTableauxSwapConnectedStatement)
    (young : YoungRepresentationActionData lam)
    (T0 T : StandardYoungTableau lam) :
    S05_averagedRejectionYoungOperator young (tableauBasisVec T) =
      fun U =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_actual young)).basisScalar T0 *
          tableauBasisVec T U := by
  exact averagedRejectionYoungOperator_scalar_on_basis hconn
    (S05_averagedRejectionYoungOperatorData_actual young) T0 T

end DictatorshipTesting
