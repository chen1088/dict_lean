import DictatorshipTesting.Paper.Defs.S05_Def5_12a_MatchingIdempotents
import DictatorshipTesting.Paper.Defs.S05_Def5_12b_GroupAlgebraAction
import Mathlib.Tactic.Group

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.Defs.S05_Def5_12d_TableauOperatorTrace`
- `DictatorshipTesting.Paper.S05_Lem5_13_MatchingSubgroupEigenbasis`
- `DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks`
-/
/-!
Paper statement: Definition 5.12 part (c) `def:matching-idempotents`
Title in paper: Matching idempotents and averaged rejection.

Status: definition plus proved covariance and centrality.  The coefficient
function is obtained by pushing the high-character Fourier kernel of each
matching cube into the symmetric group and then averaging over all ordered
near-perfect matchings.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

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
    (σ : Perm α) (M : OrderedMatching α) (x : FinCube M.edgeCount)
    (r : Fin M.edgeCount) :
    (M.relabel σ).edgePerm x r = σ * M.edgePerm x r * σ⁻¹ := by
  by_cases hx : x r
  · simp [AlgebraicLibrary.OrderedMatching.edgePerm, hx,
      orderedMatching_edgeSwap_relabel]
  · simp [AlgebraicLibrary.OrderedMatching.edgePerm, hx]

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
    (σ : Perm α) (M : OrderedMatching α) (x : FinCube M.edgeCount) :
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
    (M : OrderedMatching α) (x : FinCube M.edgeCount) : Real :=
  (∑ S ∈ S05_matchingHighCharacterSet M,
      cubeChar S x * cubeChar S (finCubeZero M.edgeCount)) /
    (Fintype.card (FinCube M.edgeCount) : Real)

/-- The coefficient function of one matching-character Fourier idempotent.
This is the pushforward of `|FinCube|⁻¹ χ_R` along the matching-cube map. -/
def S05_fixedMatchingCharacterElement {α : Type*}
    [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (R : Finset (Fin M.edgeCount)) :
    GroupAlgebraElement (Perm α) :=
  fun g => ∑ x : FinCube M.edgeCount,
    if M.tau x = g then
      cubeChar R x / (Fintype.card (FinCube M.edgeCount) : Real)
    else 0

/-- The coefficient function of the high matching idempotent for one fixed
matching.  The sum over preimages avoids requiring a separate injectivity
lemma for `M.tau`. -/
def S05_fixedMatchingHighElement {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) : GroupAlgebraElement (Perm α) :=
  fun g => ∑ x : FinCube M.edgeCount,
    if M.tau x = g then S05_matchingHighKernel M x else 0

/-- Representing a coefficient function pushed forward from one matching cube
is the same as summing the represented matching-cube elements directly. -/
theorem repOfGroupAlgebraElement_matchingCubePushforward
    {α V : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData (Perm α) V)
    (M : OrderedMatching α) (k : FinCube M.edgeCount → Real) (v : V) :
    repOfGroupAlgebraElement rep
        (fun g => ∑ x : FinCube M.edgeCount,
          if M.tau x = g then k x else 0) v =
      ∑ x : FinCube M.edgeCount, k x • rep.rho (M.tau x) v := by
  classical
  unfold repOfGroupAlgebraElement
  calc
    (∑ g : Perm α,
        (∑ x : FinCube M.edgeCount,
          if M.tau x = g then k x else 0) • rep.rho g v) =
        ∑ g : Perm α, ∑ x : FinCube M.edgeCount,
          (if M.tau x = g then k x else 0) • rep.rho g v := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_smul]
    _ = ∑ x : FinCube M.edgeCount, ∑ g : Perm α,
          (if M.tau x = g then k x else 0) • rep.rho g v := by
      rw [Finset.sum_comm]
    _ = ∑ x : FinCube M.edgeCount, k x • rep.rho (M.tau x) v := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp

/-- A represented matching-character idempotent selects precisely the
matching-character eigenspace with the same support. -/
theorem representedMatchingIdempotent_apply_eigenvector
    {α V : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData (Perm α) V)
    (M : OrderedMatching α) (R A : Finset (Fin M.edgeCount)) (v : V)
    (hv : ∀ x : FinCube M.edgeCount,
      rep.rho (M.tau x) v = cubeChar A x • v) :
    repOfGroupAlgebraElement rep
        (S05_fixedMatchingCharacterElement M R) v =
      if R = A then v else 0 := by
  classical
  rw [show S05_fixedMatchingCharacterElement M R =
      fun g => ∑ x : FinCube M.edgeCount,
        if M.tau x = g then
          cubeChar R x / (Fintype.card (FinCube M.edgeCount) : Real)
        else 0 by rfl]
  rw [repOfGroupAlgebraElement_matchingCubePushforward]
  calc
    (∑ x : FinCube M.edgeCount,
        (cubeChar R x / (Fintype.card (FinCube M.edgeCount) : Real)) •
          rep.rho (M.tau x) v) =
        ∑ x : FinCube M.edgeCount,
          ((cubeChar R x * cubeChar A x) /
            (Fintype.card (FinCube M.edgeCount) : Real)) • v := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hv x, smul_smul]
      congr 1
      ring
    _ = ((∑ x : FinCube M.edgeCount,
          cubeChar R x * cubeChar A x) /
            (Fintype.card (FinCube M.edgeCount) : Real)) • v := by
      rw [Finset.sum_div, Finset.sum_smul]
    _ = (if R = A then (1 : Real) else 0) • v := by
      rw [show
        (∑ x : FinCube M.edgeCount, cubeChar R x * cubeChar A x) /
            (Fintype.card (FinCube M.edgeCount) : Real) =
          cubeExpectation (fun x : FinCube M.edgeCount =>
            cubeChar R x * cubeChar A x) by rfl]
      rw [S02_Lem2_03_cubeChar_orthonormality]
    _ = if R = A then v else 0 := by
      split <;> simp_all

/-- The fixed high-matching coefficient element is the sum of its
high-character Fourier idempotents. -/
theorem S05_fixedMatchingHighElement_eq_sum_characterElements
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) :
    S05_fixedMatchingHighElement M =
      fun g => ∑ R ∈ S05_matchingHighCharacterSet M,
        S05_fixedMatchingCharacterElement M R g := by
  classical
  funext g
  unfold S05_fixedMatchingHighElement S05_fixedMatchingCharacterElement
    S05_matchingHighKernel
  calc
    (∑ x : FinCube M.edgeCount,
        if M.tau x = g then
          (∑ S ∈ S05_matchingHighCharacterSet M,
              cubeChar S x * cubeChar S (finCubeZero M.edgeCount)) /
            (Fintype.card (FinCube M.edgeCount) : Real)
        else 0) =
      ∑ x : FinCube M.edgeCount, ∑ S ∈ S05_matchingHighCharacterSet M,
        if M.tau x = g then
          cubeChar S x / (Fintype.card (FinCube M.edgeCount) : Real)
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : M.tau x = g
      · simp only [hx, if_pos]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro S _hS
        simp only [cubeChar, cubeZero_apply, Bool.false_eq_true, if_false,
          Finset.prod_const_one]
        ring
      · simp [hx]
    _ = ∑ S ∈ S05_matchingHighCharacterSet M,
        ∑ x : FinCube M.edgeCount,
          if M.tau x = g then
            cubeChar S x / (Fintype.card (FinCube M.edgeCount) : Real)
          else 0 := by
      rw [Finset.sum_comm]

/-- The represented fixed high-matching element is the identity on a high
matching-character eigenvector and zero on a low one. -/
theorem representedHighMatchingElement_apply_eigenvector
    {α V : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid V] [Module Real V]
    (rep : GroupRepresentationActionData (Perm α) V)
    (M : OrderedMatching α) (A : Finset (Fin M.edgeCount)) (v : V)
    (hv : ∀ x : FinCube M.edgeCount,
      rep.rho (M.tau x) v = cubeChar A x • v) :
    repOfGroupAlgebraElement rep (S05_fixedMatchingHighElement M) v =
      if S05_matchingCharacterHigh A then v else 0 := by
  classical
  rw [S05_fixedMatchingHighElement_eq_sum_characterElements]
  unfold repOfGroupAlgebraElement
  calc
    (∑ g : Perm α,
        (∑ R ∈ S05_matchingHighCharacterSet M,
          S05_fixedMatchingCharacterElement M R g) • rep.rho g v) =
      ∑ R ∈ S05_matchingHighCharacterSet M,
        repOfGroupAlgebraElement rep
          (S05_fixedMatchingCharacterElement M R) v := by
      simp only [Finset.sum_smul, repOfGroupAlgebraElement]
      rw [Finset.sum_comm]
    _ = ∑ R ∈ S05_matchingHighCharacterSet M,
        if R = A then v else 0 := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact representedMatchingIdempotent_apply_eigenvector rep M R A v hv
    _ = if S05_matchingCharacterHigh A then v else 0 := by
      by_cases hA : A ∈ S05_matchingHighCharacterSet M
      · rw [Finset.sum_eq_single A]
        · have hhigh := (S05_mem_matchingHighCharacterSet_iff M A).mp hA
          simp [hhigh]
        · intro R hR hne
          simp [hne]
        · intro hnot
          exact False.elim (hnot hA)
      · have hhigh : ¬ S05_matchingCharacterHigh A := by
          intro h
          exact hA ((S05_mem_matchingHighCharacterSet_iff M A).mpr h)
        rw [if_neg hhigh]
        apply Finset.sum_eq_zero
        intro R hR
        have hne : R ≠ A := by
          intro hRA
          apply hA
          simpa [hRA] using hR
        simp [hne]

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
      (∑ x : FinCube M.edgeCount,
        if M.tau x = g then S05_matchingHighKernel M x else 0) *
          F (π * g)) =
      ∑ S ∈ S05_matchingHighCharacterSet M,
        cubeFourierCoeff (fun x : FinCube M.edgeCount => F (π * M.tau x)) S *
          cubeChar S (finCubeZero M.edgeCount)
  calc
    (∑ g : Perm α,
      (∑ x : FinCube M.edgeCount,
        if M.tau x = g then S05_matchingHighKernel M x else 0) *
          F (π * g)) =
        ∑ g : Perm α, ∑ x : FinCube M.edgeCount,
          (if M.tau x = g then S05_matchingHighKernel M x else 0) *
            F (π * g) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_mul]
    _ = ∑ x : FinCube M.edgeCount, ∑ g : Perm α,
          (if M.tau x = g then S05_matchingHighKernel M x else 0) *
            F (π * g) := by
      rw [Finset.sum_comm]
    _ = ∑ x : FinCube M.edgeCount,
          S05_matchingHighKernel M x * F (π * M.tau x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp
    _ = ∑ x : FinCube M.edgeCount,
        ∑ S ∈ S05_matchingHighCharacterSet M,
          (F (π * M.tau x) * cubeChar S x) /
              (Fintype.card (FinCube M.edgeCount) : Real) *
            cubeChar S (finCubeZero M.edgeCount) := by
      apply Finset.sum_congr rfl
      intro x _hx
      unfold S05_matchingHighKernel
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _hS
      ring
    _ = ∑ S ∈ S05_matchingHighCharacterSet M,
        ∑ x : FinCube M.edgeCount,
          (F (π * M.tau x) * cubeChar S x) /
              (Fintype.card (FinCube M.edgeCount) : Real) *
            cubeChar S (finCubeZero M.edgeCount) := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ S05_matchingHighCharacterSet M,
        cubeFourierCoeff (fun x : FinCube M.edgeCount => F (π * M.tau x)) S *
          cubeChar S (finCubeZero M.edgeCount) := by
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

/-- The represented high-idempotent operator for one fixed near-perfect
matching on a faithful Theorem 5.3 Young action. -/
def S05_fixedMatchingRejectionYoungOperator {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) :
    TableauSpace lam -> TableauSpace lam :=
  repOfGroupAlgebraElement action.rep
    (S05_fixedMatchingHighElement M.toOrdered)

/-- The represented Fourier idempotent for one character of one fixed
near-perfect matching. -/
def S05_fixedMatchingCharacterYoungOperator {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    (R : Finset (Fin M.toOrdered.edgeCount)) :
    TableauSpace lam -> TableauSpace lam :=
  repOfGroupAlgebraElement action.rep
    (S05_fixedMatchingCharacterElement M.toOrdered R)

/-- The actual represented character idempotent selects an actual
matching-cube eigenvector with the same character support. -/
theorem S05_fixedMatchingCharacterYoungOperator_apply_eigenvector
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    (R A : Finset (Fin M.toOrdered.edgeCount)) (v : TableauSpace lam)
    (hv : ∀ x : FinCube M.toOrdered.edgeCount,
      action.rep.rho (M.toOrdered.tau x) v = cubeChar A x • v) :
    S05_fixedMatchingCharacterYoungOperator action M R v =
      if R = A then v else 0 := by
  exact representedMatchingIdempotent_apply_eigenvector
    action.rep M.toOrdered R A v hv

/-- The actual represented fixed high-matching operator is the identity on an
actual high matching-cube eigenvector and zero on a low one. -/
theorem S05_fixedMatchingRejectionYoungOperator_apply_eigenvector
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1))
    (A : Finset (Fin M.toOrdered.edgeCount)) (v : TableauSpace lam)
    (hv : ∀ x : FinCube M.toOrdered.edgeCount,
      action.rep.rho (M.toOrdered.tau x) v = cubeChar A x • v) :
    S05_fixedMatchingRejectionYoungOperator action M v =
      if S05_matchingCharacterHigh A then v else 0 := by
  exact representedHighMatchingElement_apply_eigenvector
    action.rep M.toOrdered A v hv

/-- The actual represented fixed high-matching operator is the finite sum of
the represented high-character idempotents. -/
theorem S05_fixedMatchingRejectionYoungOperator_eq_sum_characters
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (M : NearPerfectMatching (n + 1)) (v : TableauSpace lam) :
    S05_fixedMatchingRejectionYoungOperator action M v =
      ∑ R ∈ S05_matchingHighCharacterSet M.toOrdered,
        S05_fixedMatchingCharacterYoungOperator action M R v := by
  classical
  unfold S05_fixedMatchingRejectionYoungOperator
    S05_fixedMatchingCharacterYoungOperator
  rw [S05_fixedMatchingHighElement_eq_sum_characterElements]
  unfold repOfGroupAlgebraElement
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]

/-- On faithful Theorems 5.3 and 5.5 data, the concrete averaged operator is the finite
average of the represented fixed-matching high-idempotent operators. -/
theorem S05_averagedRejectionYoungOperator_eq_average_fixed
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (f : TableauSpace lam) :
    S05_averagedRejectionYoungOperator
        (YoungRepresentationActionData.ofYoungActions action content) f =
      (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ •
        ∑ M : NearPerfectMatching (n + 1),
          S05_fixedMatchingRejectionYoungOperator action M f := by
  change
    repOfGroupAlgebraElement action.rep
        (fun g =>
          (∑ M : NearPerfectMatching (n + 1),
            S05_fixedMatchingHighElement M.toOrdered g) /
              (Fintype.card (NearPerfectMatching (n + 1)) : Real)) f =
      (Fintype.card (NearPerfectMatching (n + 1)) : Real)⁻¹ •
        ∑ M : NearPerfectMatching (n + 1),
          repOfGroupAlgebraElement action.rep
            (S05_fixedMatchingHighElement M.toOrdered) f
  exact repOfGroupAlgebraElement_fintypeAverage action.rep
    (fun M : NearPerfectMatching (n + 1) =>
      S05_fixedMatchingHighElement M.toOrdered) f

/-- The actual averaged high-matching operator supplies the one-block
commutation interface for every supplied Young representation model. -/
def S05_averagedRejectionYoungOperatorData_actual {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (young : YoungRepresentationActionData lam) :
    AveragedRejectionYoungOperatorData lam :=
  averagedRejectionYoungOperatorData_of_centralGroupAlgebraElement young
    (S05_averagedHighMatchingElement (n + 1))
    (S05_averagedHighMatchingElement_central (n + 1))

/-- Faithful Section 5.1/Theorem 5.3 data constructs the concrete averaged rejection
operator package without any scalarity field in either external input. -/
def S05_averagedRejectionYoungOperatorData_from_section5
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action) :
    AveragedRejectionYoungOperatorData lam :=
  S05_averagedRejectionYoungOperatorData_actual
    (YoungRepresentationActionData.ofYoungActions action content)

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
    (young : YoungRepresentationActionData lam)
    (T0 T : StandardYoungTableau lam) :
    S05_averagedRejectionYoungOperator young (tableauBasisVec T) =
      fun U =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_actual young)).basisScalar T0 *
          tableauBasisVec T U := by
  exact averagedRejectionYoungOperator_scalar_on_basis
    (S05_averagedRejectionYoungOperatorData_actual young) T0 T

/-- Concrete one-block scalarity derived from faithful Theorems 5.3 and 5.5 data, centrality
of the actual averaged matching element, and the internally proved Lemma 5.3. -/
theorem S05_averagedRejectionYoungOperator_scalar_from_section5
    {n : Nat} {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (content : JucysMurphyContentActionData action)
    (T0 T : StandardYoungTableau lam) :
    (S05_averagedRejectionYoungOperatorData_from_section5 action content).operator
        (tableauBasisVec T) =
      fun U =>
        (AveragedRejectionYoungOperatorData.toYoungModelOperatorCommutationData
            (S05_averagedRejectionYoungOperatorData_from_section5
              action content)).basisScalar T0 * tableauBasisVec T U := by
  exact averagedRejectionYoungOperator_scalar_on_basis
    (S05_averagedRejectionYoungOperatorData_from_section5 action content) T0 T

end DictatorshipTesting
