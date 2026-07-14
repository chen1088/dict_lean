import DictatorshipTesting.Paper.Defs.S03_IntDef_OrderedMatchingTau

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S03_Int_OrderedMatchingTauMul`
- `DictatorshipTesting.Paper.S03_Lem3_01_DictatorToJunta`
-/
/-!
# Coordinate-dependence of matching cube elements
-/

namespace DictatorshipTesting

/-- If every permutation in a list fixes `a`, then the list product fixes `a`. -/
theorem list_perm_prod_apply_eq_of_forall_mem_eq {α : Type*}
    (l : List (Perm α)) (a : α)
    (h : ∀ σ ∈ l, σ a = a) :
    l.prod a = a := by
  induction l with
  | nil =>
      simp
  | cons σ l ih =>
      have htail : l.prod a = a := by
        apply ih
        intro τ hτ
        exact h τ (by simp [hτ])
      have hhead : σ a = a := h σ (by simp)
      simp [List.prod_cons, Equiv.Perm.mul_apply, htail, hhead]

/-- A matching edge-swap fixes a point not appearing in that edge. -/
theorem orderedMatching_edgeSwap_apply_of_ne {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) {a : α}
    (hl : a ≠ M.left r) (hr : a ≠ M.right r) :
    M.edgeSwap r a = a := by
  simpa [OrderedMatching.edgeSwap, pswap] using
    (Equiv.swap_apply_of_ne_of_ne hl hr)

/-- If `a` is unmatched by `M`, then every cube element fixes `a`. -/
theorem orderedMatching_tau_apply_of_unmatched {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) {a : α}
    (hleft : ∀ r : Fin M.edgeCount, a ≠ M.left r)
    (hright : ∀ r : Fin M.edgeCount, a ≠ M.right r) :
    M.tau x a = a := by
  unfold OrderedMatching.tau
  apply list_perm_prod_apply_eq_of_forall_mem_eq
  intro σ hσ
  rcases (List.mem_ofFn.mp hσ) with ⟨r, rfl⟩
  by_cases hx : x r
  · simp [OrderedMatching.edgePerm, hx,
      orderedMatching_edgeSwap_apply_of_ne M r (hleft r) (hright r)]
  · simp [OrderedMatching.edgePerm, hx]

/-- Membership in the two endpoints of one ordered matching edge. -/
def OrderedMatching.InEdge {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) (a : α) : Prop :=
  a = M.left r ∨ a = M.right r

theorem orderedMatching_edgePerm_apply_left_of_ne {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount)
    {r s : Fin M.edgeCount} (hsr : s ≠ r) :
    M.edgePerm x s (M.left r) = M.left r := by
  by_cases hx : x s
  · have hdisj := M.edges_disjoint (r := s) (s := r) hsr
    have hleft : M.left r ≠ M.left s := hdisj.1.symm
    have hright : M.left r ≠ M.right s := hdisj.2.2.1.symm
    simp [OrderedMatching.edgePerm, OrderedMatching.edgeSwap, pswap, hx,
      Equiv.swap_apply_of_ne_of_ne hleft hright]
  · simp [OrderedMatching.edgePerm, hx]

theorem orderedMatching_edgePerm_apply_right_of_ne {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount)
    {r s : Fin M.edgeCount} (hsr : s ≠ r) :
    M.edgePerm x s (M.right r) = M.right r := by
  by_cases hx : x s
  · have hdisj := M.edges_disjoint (r := s) (s := r) hsr
    have hleft : M.right r ≠ M.left s := hdisj.2.1.symm
    have hright : M.right r ≠ M.right s := hdisj.2.2.2.symm
    simp [OrderedMatching.edgePerm, OrderedMatching.edgeSwap, pswap, hx,
      Equiv.swap_apply_of_ne_of_ne hleft hright]
  · simp [OrderedMatching.edgePerm, hx]

theorem orderedMatching_edgePerm_preserves_edge {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount)
    (s r : Fin M.edgeCount) {a : α}
    (ha : M.InEdge r a) :
    M.InEdge r (M.edgePerm x s a) := by
  rcases ha with rfl | rfl
  · by_cases hsr : s = r
    · subst s
      by_cases hx : x r
      · right
        simp [OrderedMatching.edgePerm, OrderedMatching.edgeSwap, pswap, hx]
      · left
        simp [OrderedMatching.edgePerm, hx]
    · left
      exact orderedMatching_edgePerm_apply_left_of_ne M x hsr
  · by_cases hsr : s = r
    · subst s
      by_cases hx : x r
      · left
        simp [OrderedMatching.edgePerm, OrderedMatching.edgeSwap, pswap, hx]
      · right
        simp [OrderedMatching.edgePerm, hx]
    · right
      exact orderedMatching_edgePerm_apply_right_of_ne M x hsr

/-- Each single edge factor is self-inverse. -/
theorem orderedMatching_edgePerm_inv {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) (r : Fin M.edgeCount) :
    (M.edgePerm x r)⁻¹ = M.edgePerm x r := by
  by_cases hx : x r
  · simp [OrderedMatching.edgePerm, OrderedMatching.edgeSwap, pswap, hx,
      Equiv.swap_inv]
  · simp [OrderedMatching.edgePerm, hx]

theorem orderedMatching_edgePerm_apply_eq_of_same_bit_on_edge {α : Type*}
    [DecidableEq α] (M : OrderedMatching α)
    {x y : Cube M.edgeCount} {r s : Fin M.edgeCount} {a : α}
    (hxy : x r = y r) (ha : M.InEdge r a) :
    M.edgePerm x s a = M.edgePerm y s a := by
  rcases ha with rfl | rfl
  · by_cases hsr : s = r
    · subst s
      simp [OrderedMatching.edgePerm, hxy]
    · rw [orderedMatching_edgePerm_apply_left_of_ne M x hsr,
        orderedMatching_edgePerm_apply_left_of_ne M y hsr]
  · by_cases hsr : s = r
    · subst s
      simp [OrderedMatching.edgePerm, hxy]
    · rw [orderedMatching_edgePerm_apply_right_of_ne M x hsr,
        orderedMatching_edgePerm_apply_right_of_ne M y hsr]

theorem orderedMatching_list_prod_apply_eq_of_same_bit_on_edge {α : Type*}
    [DecidableEq α] (M : OrderedMatching α)
    (l : List (Fin M.edgeCount)) {x y : Cube M.edgeCount}
    {r : Fin M.edgeCount} {a : α}
    (hxy : x r = y r) (ha : M.InEdge r a) :
    ((l.map fun s => M.edgePerm x s).prod) a =
      ((l.map fun s => M.edgePerm y s).prod) a ∧
    M.InEdge r (((l.map fun s => M.edgePerm x s).prod) a) := by
  induction l with
  | nil =>
      simp [ha]
  | cons s l ih =>
      rcases ih with ⟨htail, hpair⟩
      have hhead :
          M.edgePerm x s (((l.map fun t => M.edgePerm x t).prod) a) =
            M.edgePerm y s (((l.map fun t => M.edgePerm x t).prod) a) :=
        orderedMatching_edgePerm_apply_eq_of_same_bit_on_edge M hxy hpair
      have hpres :
          M.InEdge r
            (M.edgePerm x s (((l.map fun t => M.edgePerm x t).prod) a)) :=
        orderedMatching_edgePerm_preserves_edge M x s r hpair
      simp [List.prod_cons, Equiv.Perm.mul_apply]
      rw [← htail]
      exact ⟨hhead, hpres⟩

/-- On an endpoint of edge `r`, `tau_x` depends only on the `r`th cube bit. -/
theorem orderedMatching_tau_apply_eq_of_same_bit_on_edge {α : Type*}
    [DecidableEq α] (M : OrderedMatching α)
    {x y : Cube M.edgeCount} {r : Fin M.edgeCount} {a : α}
    (hxy : x r = y r) (ha : M.InEdge r a) :
    M.tau x a = M.tau y a := by
  unfold OrderedMatching.tau
  simpa [List.ofFn_eq_map] using
    (orderedMatching_list_prod_apply_eq_of_same_bit_on_edge
      M (List.finRange M.edgeCount) hxy ha).1

/-- The inverse of `tau_x` is the reversed product of the same edge factors. -/
theorem orderedMatching_tau_symm_eq_reverse_prod {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) :
    (M.tau x).symm =
      ((List.finRange M.edgeCount).reverse.map fun r => M.edgePerm x r).prod := by
  have hmap :
      List.map (fun σ : Perm α => σ⁻¹)
          (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r) =
        List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r := by
    have hmap_id :
        List.map (fun σ : Perm α => σ⁻¹)
            (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r) =
          List.map id (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r) := by
      apply List.map_congr_left
      intro σ hσ
      rcases (List.mem_ofFn.mp hσ) with ⟨r, rfl⟩
      exact orderedMatching_edgePerm_inv M x r
    simpa using hmap_id
  calc
    (M.tau x).symm = (M.tau x)⁻¹ := (Equiv.Perm.inv_def _).symm
    _ = ((List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).prod)⁻¹ := by
      rfl
    _ =
        (List.map (fun σ : Perm α => σ⁻¹)
            (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r)).reverse.prod := by
      rw [List.prod_inv_reverse]
    _ = (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).reverse.prod := by
      rw [hmap]
    _ = ((List.finRange M.edgeCount).reverse.map fun r => M.edgePerm x r).prod := by
      rw [List.ofFn_eq_map]
      rw [← List.map_reverse]

/-- On an endpoint of edge `r`, the inverse of `tau_x` also depends only on the
`r`th cube bit. -/
theorem orderedMatching_tau_symm_apply_eq_of_same_bit_on_edge {α : Type*}
    [DecidableEq α] (M : OrderedMatching α)
    {x y : Cube M.edgeCount} {r : Fin M.edgeCount} {a : α}
    (hxy : x r = y r) (ha : M.InEdge r a) :
    (M.tau x).symm a = (M.tau y).symm a := by
  rw [orderedMatching_tau_symm_eq_reverse_prod M x,
    orderedMatching_tau_symm_eq_reverse_prod M y]
  exact (orderedMatching_list_prod_apply_eq_of_same_bit_on_edge
    M (List.finRange M.edgeCount).reverse hxy ha).1

/-- If `a` is unmatched by `M`, then the inverse cube element also fixes `a`. -/
theorem orderedMatching_tau_symm_apply_of_unmatched {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) {a : α}
    (hleft : ∀ r : Fin M.edgeCount, a ≠ M.left r)
    (hright : ∀ r : Fin M.edgeCount, a ≠ M.right r) :
    (M.tau x).symm a = a := by
  rw [orderedMatching_tau_symm_eq_reverse_prod M x]
  apply list_perm_prod_apply_eq_of_forall_mem_eq
  intro σ hσ
  rcases (List.mem_map.mp hσ) with ⟨r, _hr, rfl⟩
  by_cases hx : x r
  · simp [OrderedMatching.edgePerm, hx,
      orderedMatching_edgeSwap_apply_of_ne M r (hleft r) (hright r)]
  · simp [OrderedMatching.edgePerm, hx]

end DictatorshipTesting
