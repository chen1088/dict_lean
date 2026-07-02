import DictatorshipTesting.Paper.Defs

/-!
Paper statement: Theorem 2.1 (`thm:boolean-u1`)
Title in paper: Structural input: Boolean degree-one functions on S_n.

Status: external structural input.
-/

/-!
# Structural input for Theorem 2.1

This file isolates the external classification theorem used by the paper:
Boolean functions in the first permutation module are dictators.
-/

namespace DictatorshipTesting

/-- Image dictators lie in `U₁`, directly from the spanning one-cosets. -/
theorem imageDictator_mem_U1 {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsImageDictator f) :
    boolFnToReal f ∈ U1 α := by
  classical
  rcases hf with ⟨i, h, hf⟩
  let G : Perm α → ℝ :=
    ∑ j : α, (if h j then (1 : ℝ) else 0) • oneCosetReal i j
  have hG_mem : G ∈ U1 α := by
    refine Submodule.sum_mem _ ?_
    intro j _hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have h_eq : boolFnToReal f = G := by
    funext π
    rw [boolFnToReal, hf π]
    change boolToReal (h (π i)) =
      (∑ j : α, ((if h j then (1 : ℝ) else 0) • oneCosetReal i j)) π
    rw [Finset.sum_apply]
    symm
    calc
      (∑ j : α, ((if h j then (1 : ℝ) else 0) • oneCosetReal i j) π) =
          ((if h (π i) then (1 : ℝ) else 0) • oneCosetReal i (π i)) π := by
        refine Finset.sum_eq_single (s := Finset.univ)
          (f := fun j : α =>
            (((if h j then (1 : ℝ) else 0) • oneCosetReal i j) π))
          (a := π i) ?_ ?_
        · intro j _hj hj
          have hne : π i ≠ j := by
            intro hπ
            exact hj hπ.symm
          simp [oneCosetReal, hne]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = boolToReal (h (π i)) := by
        by_cases hp : h (π i) <;> simp [boolToReal, oneCosetReal, hp]
  simpa [h_eq] using hG_mem

/-- Preimage dictators lie in `U₁`, by the same one-coset expansion. -/
theorem preimageDictator_mem_U1 {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsPreimageDictator f) :
    boolFnToReal f ∈ U1 α := by
  classical
  rcases hf with ⟨j, h, hf⟩
  let G : Perm α → ℝ :=
    ∑ i : α, (if h i then (1 : ℝ) else 0) • oneCosetReal i j
  have hG_mem : G ∈ U1 α := by
    refine Submodule.sum_mem _ ?_
    intro i _hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have h_eq : boolFnToReal f = G := by
    funext π
    rw [boolFnToReal, hf π]
    change boolToReal (h (π.symm j)) =
      (∑ i : α, ((if h i then (1 : ℝ) else 0) • oneCosetReal i j)) π
    rw [Finset.sum_apply]
    symm
    calc
      (∑ i : α, ((if h i then (1 : ℝ) else 0) • oneCosetReal i j) π) =
          ((if h (π.symm j) then (1 : ℝ) else 0) •
            oneCosetReal (π.symm j) j) π := by
        refine Finset.sum_eq_single (s := Finset.univ)
          (f := fun i : α =>
            (((if h i then (1 : ℝ) else 0) • oneCosetReal i j) π))
          (a := π.symm j) ?_ ?_
        · intro i _hi hi
          have hne : π i ≠ j := by
            intro hij
            apply hi
            simpa using congrArg π.symm hij
          simp [oneCosetReal, hne]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = boolToReal (h (π.symm j)) := by
        by_cases hp : h (π.symm j) <;> simp [boolToReal, oneCosetReal, hp]
  simpa [h_eq] using hG_mem

/-- Every dictator lies in `U₁`. -/
theorem dictator_mem_U1 {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) (hf : IsDictator f) :
    boolFnToReal f ∈ U1 α := by
  rcases hf with hf | hf
  · exact imageDictator_mem_U1 f hf
  · exact preimageDictator_mem_U1 f hf

/-- On the one-point symmetric group, every Boolean function is a dictator. -/
theorem isDictator_fin_one (f : BoolFn (Fin 1)) : IsDictator f := by
  left
  refine ⟨0, fun _ : Fin 1 => f 1, ?_⟩
  intro π
  have hπ : π = 1 := Subsingleton.elim _ _
  simp [hπ]

/-- A permutation of a two-point type is determined by where it sends `0`. -/
theorem perm_fin_two_eq_pswap_zero_apply_zero (π : Perm (Fin 2)) :
    π = pswap 0 (π 0) := by
  ext x
  fin_cases x
  · simp [pswap]
  · have hπ0_ne_π1 : π 0 ≠ π 1 := by
      intro h
      have hpre := congrArg π.symm h
      norm_num at hpre
    have hneval : (π 0).val ≠ (π 1).val := by
      intro hval
      exact hπ0_ne_π1 (Fin.ext hval)
    have hcase : (π 0).val = 0 ∨ (π 0).val = 1 := by omega
    rcases hcase with h0 | h0
    · have hp0 : π 0 = (0 : Fin 2) := Fin.ext h0
      have hp1 : (π 1).val = 1 := by omega
      simpa [pswap, hp0] using hp1
    · have hp0 : π 0 = (1 : Fin 2) := Fin.ext h0
      have hp1 : (π 1).val = 0 := by omega
      simpa [pswap, hp0] using hp1

/-- On the two-point symmetric group, every Boolean function is a dictator. -/
theorem isDictator_fin_two (f : BoolFn (Fin 2)) : IsDictator f := by
  left
  refine ⟨0, fun x : Fin 2 => f (pswap 0 x), ?_⟩
  intro π
  exact congrArg f (perm_fin_two_eq_pswap_zero_apply_zero π)

/-- External structural input behind the nontrivial direction of Theorem 2.1.
The statement is restricted to `3 ≤ n`: `n = 1` and `n = 2` are proved directly,
while for `n = 0` the zero Boolean function lies in `U₁` but is not a dictator. -/
theorem booleanU1_dictator_classification_input (n : ℕ) (hn : 3 ≤ n)
    (f : BoolFn (Fin n)) :
    boolFnToReal f ∈ U1 (Fin n) → IsDictator f := by
  sorry

/-- Theorem 2.1, `thm:boolean-u1`: Boolean functions in `U₁` are exactly
dictators.  This preserves the old theorem name while keeping the proof
boundary in the paper-numbered file. -/
theorem Thm2_1_BooleanU1 (n : ℕ) (hn : 1 ≤ n) (f : BoolFn (Fin n)) :
    boolFnToReal f ∈ U1 (Fin n) ↔ IsDictator f := by
  constructor
  · intro hf
    by_cases hn1 : n = 1
    · subst n
      exact isDictator_fin_one f
    · by_cases hn2 : n = 2
      · subst n
        exact isDictator_fin_two f
      · have hn3 : 3 ≤ n := by omega
        exact booleanU1_dictator_classification_input n hn3 f hf
  · exact dictator_mem_U1 f

end DictatorshipTesting
