import DictatorshipTesting.Paper.Aux_ListPermProdFixes

/-!
# Unmatched points in a matching cube
-/

namespace DictatorshipTesting

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

end DictatorshipTesting
