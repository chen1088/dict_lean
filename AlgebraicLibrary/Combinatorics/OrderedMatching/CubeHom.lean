import AlgebraicLibrary.Combinatorics.OrderedMatching.Dependence

/-! The Boolean-cube homomorphism associated to an ordered matching. -/

namespace AlgebraicLibrary

/-- A cube supported on one coordinate, with prescribed bit. -/
def cubeSingleBit {ι : Type*} [DecidableEq ι] (r : ι) (b : Bool) : Cube ι :=
  fun s => if s = r then b else false

/-- The matching product of a single-bit cube is its single edge factor. -/
theorem orderedMatching_tau_singleBit {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) (b : Bool) :
    M.tau (cubeSingleBit r b) = M.edgePerm (cubeSingleBit r b) r := by
  unfold OrderedMatching.tau
  rw [List.ofFn_eq_map]
  calc
    ((List.finRange M.edgeCount).map
        fun s : Fin M.edgeCount => M.edgePerm (cubeSingleBit r b) s).prod =
        (M.edgePerm (cubeSingleBit r b) r) ^
          List.count r (List.finRange M.edgeCount) := by
      apply List.prod_map_eq_pow_single
      intro s hsr _hs
      simp [OrderedMatching.edgePerm, cubeSingleBit, hsr]
    _ = M.edgePerm (cubeSingleBit r b) r := by
      simp [List.count_finRange]

/-- Exact action on the left endpoint of an edge. -/
theorem orderedMatching_tau_apply_left {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : M.EdgeCube) (r : Fin M.edgeCount) :
    M.tau x (M.left r) = if x r then M.right r else M.left r := by
  let y : M.EdgeCube := cubeSingleBit r (x r)
  have hxy : x r = y r := by simp [y, cubeSingleBit]
  have hdep : M.tau x (M.left r) = M.tau y (M.left r) :=
    orderedMatching_tau_apply_eq_of_same_bit_on_edge M hxy (Or.inl rfl)
  rw [hdep, orderedMatching_tau_singleBit M r (x r)]
  by_cases hx : x r
  · simp [cubeSingleBit, OrderedMatching.edgePerm, OrderedMatching.edgeSwap, hx]
  · simp [cubeSingleBit, OrderedMatching.edgePerm, hx]

/-- Exact action on the right endpoint of an edge. -/
theorem orderedMatching_tau_apply_right {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : M.EdgeCube) (r : Fin M.edgeCount) :
    M.tau x (M.right r) = if x r then M.left r else M.right r := by
  let y : M.EdgeCube := cubeSingleBit r (x r)
  have hxy : x r = y r := by simp [y, cubeSingleBit]
  have hdep : M.tau x (M.right r) = M.tau y (M.right r) :=
    orderedMatching_tau_apply_eq_of_same_bit_on_edge M hxy (Or.inr rfl)
  rw [hdep, orderedMatching_tau_singleBit M r (x r)]
  by_cases hx : x r
  · simp [cubeSingleBit, OrderedMatching.edgePerm, OrderedMatching.edgeSwap, hx]
  · simp [cubeSingleBit, OrderedMatching.edgePerm, hx]

/-- Matching-cube elements multiply according to coordinatewise xor. -/
theorem orderedMatching_tau_mul {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x y : M.EdgeCube) :
    M.tau x * M.tau y = M.tau (cubeXor x y) := by
  ext a
  by_cases hleft : ∃ r : Fin M.edgeCount, a = M.left r
  · rcases hleft with ⟨r, rfl⟩
    by_cases hx : x r <;> by_cases hy : y r <;>
      simp [Equiv.Perm.mul_apply, orderedMatching_tau_apply_left,
        orderedMatching_tau_apply_right, cubeXor, hx, hy]
  · by_cases hright : ∃ r : Fin M.edgeCount, a = M.right r
    · rcases hright with ⟨r, rfl⟩
      by_cases hx : x r <;> by_cases hy : y r <;>
        simp [Equiv.Perm.mul_apply, orderedMatching_tau_apply_left,
          orderedMatching_tau_apply_right, cubeXor, hx, hy]
    · have hleft_all : ∀ r : Fin M.edgeCount, a ≠ M.left r := by
        intro r h
        exact hleft ⟨r, h⟩
      have hright_all : ∀ r : Fin M.edgeCount, a ≠ M.right r := by
        intro r h
        exact hright ⟨r, h⟩
      simp [Equiv.Perm.mul_apply,
        orderedMatching_tau_apply_of_unmatched M x hleft_all hright_all,
        orderedMatching_tau_apply_of_unmatched M y hleft_all hright_all,
        orderedMatching_tau_apply_of_unmatched M (cubeXor x y) hleft_all hright_all]

/-- The matching-cube element at the origin is the identity permutation. -/
theorem orderedMatching_tau_zero {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) :
    M.tau (cubeZero (Fin M.edgeCount)) = 1 := by
  ext a
  by_cases hleft : ∃ r : Fin M.edgeCount, a = M.left r
  · rcases hleft with ⟨r, rfl⟩
    simp [orderedMatching_tau_apply_left, cubeZero]
  · by_cases hright : ∃ r : Fin M.edgeCount, a = M.right r
    · rcases hright with ⟨r, rfl⟩
      simp [orderedMatching_tau_apply_right, cubeZero]
    · have hleft_all : ∀ r : Fin M.edgeCount, a ≠ M.left r := by
        intro r h
        exact hleft ⟨r, h⟩
      have hright_all : ∀ r : Fin M.edgeCount, a ≠ M.right r := by
        intro r h
        exact hright ⟨r, h⟩
      simp [orderedMatching_tau_apply_of_unmatched M (cubeZero (Fin M.edgeCount))
        hleft_all hright_all]

end AlgebraicLibrary
