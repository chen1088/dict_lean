import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.Defs.S05_IntDef_JucysMurphyContentActionData
import Mathlib.Algebra.Group.End

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Lem5_04_JucysMurphyRecurrences`
- `DictatorshipTesting.Paper.S05_Thm5_05_JucysMurphyContentAction`
-/

/-!
Internal proof of the faithful Section 5.2 content action.  The argument first
proves the type-A Jucys--Murphy recurrence at the coefficient-function level,
then proves its matching recurrence for the concrete tableau operators.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Conjugating a transposition ending at `a+1` by the adjacent swap `s_a`
moves that endpoint down to `a`. -/
theorem s05_adjacent_conjugate_swap_hi_to_lo {n : Nat}
    (a : Fin n) {i : Fin (n + 1)} (hi : i < a.castSucc) :
    s05_adjacentTransposition a * Equiv.swap i a.succ *
        s05_adjacentTransposition a =
      Equiv.swap i a.castSucc := by
  let s := s05_adjacentTransposition a
  have hi_ne_lo : i ≠ a.castSucc := ne_of_lt hi
  have hi_ne_hi : i ≠ a.succ :=
    ne_of_lt (lt_trans hi (by simp))
  have hs_inv : s⁻¹ = s := by
    simp [s, s05_adjacentTransposition]
  have hsi : s i = i := by
    exact Equiv.swap_apply_of_ne_of_ne hi_ne_lo hi_ne_hi
  have hshi : s a.succ = a.castSucc := by
    simp [s, s05_adjacentTransposition]
  change s * Equiv.swap i a.succ * s = Equiv.swap i a.castSucc
  calc
    s * Equiv.swap i a.succ * s =
        s * Equiv.swap i a.succ * s⁻¹ := by rw [hs_inv]
    _ = Equiv.swap (s i) (s a.succ) :=
      (Equiv.swap_apply_apply s i a.succ).symm
    _ = Equiv.swap i a.castSucc := by rw [hsi, hshi]

/-- Conjugation by one adjacent transposition is an involution. -/
theorem s05_adjacent_conjugation_involutive {n : Nat} (a : Fin n) :
    Function.Involutive
      (fun g : Perm (Fin (n + 1)) =>
        s05_adjacentTransposition a * g * s05_adjacentTransposition a) := by
  intro g
  simp [s05_adjacentTransposition, mul_assoc]

/-- Equality with `(i,a+1)` is equivalent to equality with `(i,a)` after
conjugation by the adjacent swap `s_a`. -/
theorem eq_swap_hi_iff_adjacent_conjugate_eq_swap_lo {n : Nat}
    (a : Fin n) {i : Fin (n + 1)} (hi : i < a.castSucc)
    (g : Perm (Fin (n + 1))) :
    g = Equiv.swap i a.succ ↔
      s05_adjacentTransposition a * g * s05_adjacentTransposition a =
        Equiv.swap i a.castSucc := by
  let conj : Perm (Fin (n + 1)) -> Perm (Fin (n + 1)) :=
    fun h => s05_adjacentTransposition a * h * s05_adjacentTransposition a
  have hconj : conj (Equiv.swap i a.succ) = Equiv.swap i a.castSucc :=
    s05_adjacent_conjugate_swap_hi_to_lo a hi
  constructor
  · intro hg
    simpa [hg] using hconj
  · intro hg
    apply (s05_adjacent_conjugation_involutive a).injective
    exact hg.trans hconj.symm

/-- Coefficient-function form of `J_(a+1) = s_a J_a s_a + s_a`. -/
theorem s05_jucysMurphyElement_succ_recurrence {n : Nat}
    (a : Fin n) (g : Perm (Fin (n + 1))) :
    s05_jucysMurphyElement a.succ g =
      s05_jucysMurphyElement a.castSucc
          (s05_adjacentTransposition a * g * s05_adjacentTransposition a) +
        if g = s05_adjacentTransposition a then 1 else 0 := by
  classical
  let lo : Fin (n + 1) := a.castSucc
  let hi : Fin (n + 1) := a.succ
  let s : Perm (Fin (n + 1)) := s05_adjacentTransposition a
  have hfilter :
      Finset.univ.filter (fun i : Fin (n + 1) => i < hi) =
        insert lo (Finset.univ.filter fun i : Fin (n + 1) => i < lo) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hil
      by_cases hiloeq : i = lo
      · exact Or.inl hiloeq
      · exact Or.inr (by
          change (i : Nat) < (lo : Nat)
          change (i : Nat) < (hi : Nat) at hil
          have hneval : (i : Nat) ≠ (lo : Nat) := by
            intro h
            exact hiloeq (Fin.ext h)
          have hstep : (hi : Nat) = (lo : Nat) + 1 := by
            simp [lo, hi]
          omega)
    · rintro (rfl | hil)
      · simp [lo, hi]
      · change (i : Nat) < (hi : Nat)
        change (i : Nat) < (lo : Nat) at hil
        have hstep : (hi : Nat) = (lo : Nat) + 1 := by
          simp [lo, hi]
        omega
  have hlo_not_mem :
      lo ∉ Finset.univ.filter (fun i : Fin (n + 1) => i < lo) := by
    simp
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < lo),
        if g = Equiv.swap i hi then (1 : Real) else 0) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < lo),
        if s * g * s = Equiv.swap i lo then (1 : Real) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi_mem
    have hil : i < lo := (Finset.mem_filter.mp hi_mem).2
    have hiff := eq_swap_hi_iff_adjacent_conjugate_eq_swap_lo a hil g
    change (if g = Equiv.swap i a.succ then (1 : Real) else 0) =
      if s05_adjacentTransposition a * g * s05_adjacentTransposition a =
          Equiv.swap i a.castSucc then (1 : Real) else 0
    exact if_congr hiff rfl rfl
  unfold s05_jucysMurphyElement
  change
    (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < hi),
      if g = Equiv.swap i hi then (1 : Real) else 0) = _
  rw [hfilter, Finset.sum_insert hlo_not_mem]
  change
    (if g = Equiv.swap lo hi then (1 : Real) else 0) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < lo),
          if g = Equiv.swap i hi then (1 : Real) else 0) = _
  rw [hsum]
  simp only [lo, hi, s]
  rw [show Equiv.swap a.castSucc a.succ = s05_adjacentTransposition a by rfl]
  ring

/-- The coefficient recurrence transported through any supplied Theorem 5.3
representation. -/
theorem represented_jucysMurphy_succ_recurrence {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) (a : Fin n)
    (f : TableauSpace lam) :
    (∑ g : Perm (Fin (n + 1)),
        s05_jucysMurphyElement a.succ g • action.rep.rho g f) =
      action.rep.rho (s05_adjacentTransposition a)
          (∑ g : Perm (Fin (n + 1)),
            s05_jucysMurphyElement a.castSucc g •
              action.rep.rho g
                (action.rep.rho (s05_adjacentTransposition a) f)) +
        action.rep.rho (s05_adjacentTransposition a) f := by
  classical
  let s : Perm (Fin (n + 1)) := s05_adjacentTransposition a
  let conjEquiv : Perm (Fin (n + 1)) ≃ Perm (Fin (n + 1)) :=
    { toFun := fun g => s * g * s
      invFun := fun g => s * g * s
      left_inv := s05_adjacent_conjugation_involutive a
      right_inv := s05_adjacent_conjugation_involutive a }
  have hconjSum :
      (∑ g : Perm (Fin (n + 1)),
        s05_jucysMurphyElement a.castSucc (s * g * s) •
          action.rep.rho g f) =
      ∑ g : Perm (Fin (n + 1)),
        s05_jucysMurphyElement a.castSucc g •
          action.rep.rho (s * g * s) f := by
    have hsum := Equiv.sum_comp conjEquiv
      (fun g : Perm (Fin (n + 1)) =>
        s05_jucysMurphyElement a.castSucc (s * g * s) •
          action.rep.rho g f)
    calc
      (∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc (s * g * s) •
            action.rep.rho g f) =
          ∑ g : Perm (Fin (n + 1)),
            s05_jucysMurphyElement a.castSucc
                (s * (s * g * s) * s) •
              action.rep.rho (s * g * s) f := hsum.symm
      _ = ∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc g •
            action.rep.rho (s * g * s) f := by
        apply Finset.sum_congr rfl
        intro g _hg
        rw [show s * (s * g * s) * s = g by
          exact s05_adjacent_conjugation_involutive a g]
  have hrep (g : Perm (Fin (n + 1))) :
      action.rep.rho (s * g * s) f =
        action.rep.rho s (action.rep.rho g (action.rep.rho s f)) := by
    calc
      action.rep.rho (s * g * s) f =
          action.rep.rho (s * (g * s)) f := by rw [mul_assoc]
      _ = action.rep.rho s (action.rep.rho (g * s) f) :=
        action.rep.map_mul s (g * s) f
      _ = action.rep.rho s
          (action.rep.rho g (action.rep.rho s f)) := by
        rw [action.rep.map_mul g s f]
  calc
    (∑ g : Perm (Fin (n + 1)),
        s05_jucysMurphyElement a.succ g • action.rep.rho g f) =
        ∑ g : Perm (Fin (n + 1)),
          (s05_jucysMurphyElement a.castSucc (s * g * s) +
              if g = s then 1 else 0) • action.rep.rho g f := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [s05_jucysMurphyElement_succ_recurrence a g]
    _ =
        (∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc (s * g * s) •
            action.rep.rho g f) +
        ∑ g : Perm (Fin (n + 1)),
          (if g = s then (1 : Real) else 0) • action.rep.rho g f := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _hg
      rw [add_smul]
    _ =
        (∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc g •
            action.rep.rho (s * g * s) f) +
          action.rep.rho s f := by
      rw [hconjSum]
      simp
    _ =
        (∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc g •
            action.rep.rho s
              (action.rep.rho g (action.rep.rho s f))) +
          action.rep.rho s f := by
      apply congrArg (fun x => x + action.rep.rho s f)
      apply Finset.sum_congr rfl
      intro g _hg
      rw [hrep]
    _ = action.rep.rho s
          (∑ g : Perm (Fin (n + 1)),
            s05_jucysMurphyElement a.castSucc g •
              action.rep.rho g (action.rep.rho s f)) +
        action.rep.rho s f := by
      apply congrArg (fun x => x + action.rep.rho s f)
      change
        (∑ g : Perm (Fin (n + 1)),
          s05_jucysMurphyElement a.castSucc g •
            action.rep.linearMap s
              (action.rep.rho g (action.rep.rho s f))) =
          action.rep.linearMap s
            (∑ g : Perm (Fin (n + 1)),
              s05_jucysMurphyElement a.castSucc g •
                action.rep.rho g (action.rep.rho s f))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro g _hg
      rw [map_smul]
    _ = _ := rfl

/-- The diagonal content operator is additive. -/
theorem jucysMurphyDiagonalOperator_add {n : Nat}
    {lam : YoungDiagram n} (a : Fin n) (f h : TableauSpace lam) :
    jucysMurphyDiagonalOperator a (f + h) =
      jucysMurphyDiagonalOperator a f +
        jucysMurphyDiagonalOperator a h := by
  funext T
  simp [jucysMurphyDiagonalOperator, mul_add]

/-- The diagonal content operator is homogeneous. -/
theorem jucysMurphyDiagonalOperator_smul {n : Nat}
    {lam : YoungDiagram n} (a : Fin n) (c : Real) (f : TableauSpace lam) :
    jucysMurphyDiagonalOperator a (fun T => c * f T) =
      fun T => c * jucysMurphyDiagonalOperator a f T := by
  funext T
  change (entryContent T a : Real) * (c * f T) =
    c * ((entryContent T a : Real) * f T)
  ring

/-- The diagonal content operator commutes with finite coordinate sums. -/
theorem jucysMurphyDiagonalOperator_sum {n : Nat} {ι : Type*}
    {lam : YoungDiagram n} [Fintype ι]
    (a : Fin n) (f : ι -> TableauSpace lam) :
    jucysMurphyDiagonalOperator a (fun T => ∑ i, f i T) =
      fun T => ∑ i, jucysMurphyDiagonalOperator a (f i) T := by
  classical
  funext T
  simp [jucysMurphyDiagonalOperator, Finset.mul_sum]

/-- Basis-vector form of `C_(a+1) S_a = S_a C_a + I`. -/
theorem youngAdjacent_content_intertwining_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) :
    jucysMurphyDiagonalOperator a.succ
        (youngAdjacentOperator a (tableauBasisVec T)) =
      youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc (tableauBasisVec T)) +
        tableauBasisVec T := by
  have hhi : a.succ = adjacentEntryHi a := Fin.ext rfl
  by_cases hrow : adjacentSameRow T a
  · rw [youngAdjacentOperator_basis_sameRow T a hrow,
      jucysMurphyDiagonalOperator_basis_eigen,
      jucysMurphyDiagonalOperator_basis_eigen,
      youngAdjacentOperator_smul,
      youngAdjacentOperator_basis_sameRow T a hrow]
    have hcInt :=
      adjacent_content_hi_eq_lo_add_one_of_sameRow
        T a hrow
    have hc : (entryContent T a.succ : Real) =
        (entryContent T a.castSucc : Real) + 1 := by
      rw [hhi]
      exact_mod_cast hcInt
    funext U
    change (entryContent T a.succ : Real) * tableauBasisVec T U =
      (entryContent T a.castSucc : Real) * tableauBasisVec T U +
        tableauBasisVec T U
    rw [hc]
    ring
  · by_cases hcol : adjacentSameCol T a
    · rw [youngAdjacentOperator_basis_sameCol T a hcol]
      rw [jucysMurphyDiagonalOperator_basis_eigen,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_sameCol T a hcol]
      have hcInt :=
        adjacent_content_hi_eq_lo_sub_one_of_sameCol
          T a hcol
      have hc : (entryContent T a.succ : Real) =
          (entryContent T a.castSucc : Real) - 1 := by
        rw [hhi]
        exact_mod_cast hcInt
      funext U
      change (entryContent U a.succ : Real) * (-tableauBasisVec T U) =
        (entryContent T a.castSucc : Real) *
            (-tableauBasisVec T U) + tableauBasisVec T U
      by_cases hUT : U = T
      · subst U
        rw [tableauBasisVec_self, hc]
        ring
      · rw [tableauBasisVec_ne hUT]
        ring
    · let T' := adjacentSwapTableau T a hrow hcol
      let d := youngAdjacentDiagCoeff T a
      let o := youngAdjacentOffCoeff T a
      rw [youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
      rw [jucysMurphyDiagonalOperator_basis_eigen,
        youngAdjacentOperator_smul,
        youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
      have hT'ne : T' ≠ T := by
        simpa [T'] using adjacentSwapTableau_ne_self T a hrow hcol
      have hcSwapInt : entryContent T' a.succ =
          entryContent T a.castSucc := by
        rw [hhi]
        exact S05_Lem5_01_adjacentSwapTableau_entryContent_hi T a hrow hcol
      have hcSwap : (entryContent T' a.succ : Real) =
          (entryContent T a.castSucc : Real) := by
        exact_mod_cast hcSwapInt
      have haxialInt : adjacentAxialDistance T a ≠ 0 :=
        adjacentAxialDistance_ne_zero_of_swappable T a hrow hcol
      have haxialReal : ((adjacentAxialDistance T a : Int) : Real) ≠ 0 := by
        exact_mod_cast haxialInt
      have hdiff :
          (entryContent T a.succ : Real) -
              (entryContent T a.castSucc : Real) =
            ((adjacentAxialDistance T a : Int) : Real) := by
        rw [hhi]
        norm_cast
      have hd : d *
          ((entryContent T a.succ : Real) -
            (entryContent T a.castSucc : Real)) = 1 := by
        rw [hdiff]
        change ((adjacentAxialDistance T a : Int) : Real)⁻¹ *
            ((adjacentAxialDistance T a : Int) : Real) = 1
        exact inv_mul_cancel₀ haxialReal
      funext U
      change (entryContent U a.succ : Real) *
          (d * tableauBasisVec T U + o * tableauBasisVec T' U) =
        (entryContent T a.castSucc : Real) *
            (d * tableauBasisVec T U + o * tableauBasisVec T' U) +
          tableauBasisVec T U
      by_cases hUT : U = T
      · subst U
        rw [tableauBasisVec_self, tableauBasisVec_ne hT'ne.symm]
        have hd' : (entryContent T a.succ : Real) * d =
            (entryContent T a.castSucc : Real) * d + 1 := by
          nlinarith [hd]
        nlinarith
      · by_cases hUT' : U = T'
        · subst U
          rw [tableauBasisVec_ne hT'ne, tableauBasisVec_self]
          rw [hcSwap]
          ring
        · rw [tableauBasisVec_ne hUT, tableauBasisVec_ne hUT']
          ring

/-- The content intertwining identity on a scalar multiple of one tableau
basis vector. -/
theorem youngAdjacent_content_intertwining_smul_basis {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (T : StandardYoungTableau lam) (a : Fin n) (c : Real) :
    jucysMurphyDiagonalOperator a.succ
        (youngAdjacentOperator a (fun U => c * tableauBasisVec T U)) =
      youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc
            (fun U => c * tableauBasisVec T U)) +
        (fun U => c * tableauBasisVec T U) := by
  calc
    jucysMurphyDiagonalOperator a.succ
        (youngAdjacentOperator a (fun U => c * tableauBasisVec T U)) =
        (fun U => c *
          jucysMurphyDiagonalOperator a.succ
            (youngAdjacentOperator a (tableauBasisVec T)) U) := by
              rw [youngAdjacentOperator_smul,
                jucysMurphyDiagonalOperator_smul]
    _ = (fun U => c *
          (youngAdjacentOperator a
              (jucysMurphyDiagonalOperator a.castSucc
                (tableauBasisVec T)) + tableauBasisVec T) U) := by
            rw [youngAdjacent_content_intertwining_basis T a]
    _ = youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc
            (fun U => c * tableauBasisVec T U)) +
        (fun U => c * tableauBasisVec T U) := by
            rw [jucysMurphyDiagonalOperator_smul,
              youngAdjacentOperator_smul]
            funext U
            change c *
                (youngAdjacentOperator a
                    (jucysMurphyDiagonalOperator a.castSucc
                      (tableauBasisVec T)) U +
                  tableauBasisVec T U) =
              c * youngAdjacentOperator a
                    (jucysMurphyDiagonalOperator a.castSucc
                      (tableauBasisVec T)) U +
                c * tableauBasisVec T U
            ring

/-- Operator form of `C_(a+1) S_a = S_a C_a + I`. -/
theorem youngAdjacent_content_intertwining {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    jucysMurphyDiagonalOperator a.succ (youngAdjacentOperator a f) =
      youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc f) + f := by
  classical
  have hf := tableauBasis_expansion f
  calc
    jucysMurphyDiagonalOperator a.succ (youngAdjacentOperator a f) =
        jucysMurphyDiagonalOperator a.succ
          (youngAdjacentOperator a
            (fun U => ∑ T : StandardYoungTableau lam,
              f T * tableauBasisVec T U)) := by
                exact congrArg
                  (fun g => jucysMurphyDiagonalOperator a.succ
                    (youngAdjacentOperator a g)) hf
    _ = jucysMurphyDiagonalOperator a.succ
          (fun U => ∑ T : StandardYoungTableau lam,
            youngAdjacentOperator a
              (fun V => f T * tableauBasisVec T V) U) := by
                rw [youngAdjacentOperator_sum]
    _ = (fun U => ∑ T : StandardYoungTableau lam,
          jucysMurphyDiagonalOperator a.succ
            (youngAdjacentOperator a
              (fun V => f T * tableauBasisVec T V)) U) := by
                rw [jucysMurphyDiagonalOperator_sum]
    _ = (fun U => ∑ T : StandardYoungTableau lam,
          (youngAdjacentOperator a
              (jucysMurphyDiagonalOperator a.castSucc
                (fun V => f T * tableauBasisVec T V)) +
            (fun V => f T * tableauBasisVec T V)) U) := by
                funext U
                apply Finset.sum_congr rfl
                intro T _hT
                rw [youngAdjacent_content_intertwining_smul_basis T a (f T)]
    _ = (fun U =>
          (∑ T : StandardYoungTableau lam,
            youngAdjacentOperator a
              (jucysMurphyDiagonalOperator a.castSucc
                (fun V => f T * tableauBasisVec T V)) U) +
          ∑ T : StandardYoungTableau lam,
            f T * tableauBasisVec T U) := by
                funext U
                change (∑ T : StandardYoungTableau lam,
                    (youngAdjacentOperator a
                        (jucysMurphyDiagonalOperator a.castSucc
                          (fun V => f T * tableauBasisVec T V)) U +
                      f T * tableauBasisVec T U)) = _
                rw [Finset.sum_add_distrib]
    _ = youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc
            (fun U => ∑ T : StandardYoungTableau lam,
              f T * tableauBasisVec T U)) +
        (fun U => ∑ T : StandardYoungTableau lam,
          f T * tableauBasisVec T U) := by
                rw [jucysMurphyDiagonalOperator_sum]
                rw [youngAdjacentOperator_sum]
                funext U
                rfl
    _ = youngAdjacentOperator a
          (jucysMurphyDiagonalOperator a.castSucc f) + f := by
                rw [← hf]

/-- Tableau-operator form of the Jucys--Murphy recurrence:
`S_a C_a S_a + S_a = C_(a+1)`. -/
theorem youngAdjacent_content_succ_recurrence {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (a : Fin n) (f : TableauSpace lam) :
    youngAdjacentOperator a
        (jucysMurphyDiagonalOperator a.castSucc
          (youngAdjacentOperator a f)) +
      youngAdjacentOperator a f =
        jucysMurphyDiagonalOperator a.succ f := by
  have h := youngAdjacent_content_intertwining a
    (youngAdjacentOperator a f)
  rw [youngAdjacentOperator_sq a f] at h
  exact h.symm

/-- Entry zero of a standard tableau occupies the northwest cell. -/
theorem cellOfEntry_zero_row_col {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    YoungCell.row (cellOfEntry T 0) = 0 ∧
      YoungCell.col (cellOfEntry T 0) = 0 := by
  let u := cellOfEntry T 0
  have huEntry : T.entry u = 0 := by
    simpa [u] using entry_cellOfEntry T (0 : Fin (n + 1))
  have huBox : YoungCell.col u < youngRow lam (YoungCell.row u) := by
    simpa [IsYoungBox, YoungCell.toNatPair] using YoungCell.isYoungBox u
  have hrow : YoungCell.row u = 0 := by
    by_contra hne
    have hrpos : 0 < YoungCell.row u := Nat.pos_of_ne_zero hne
    let rPrev := YoungCell.row u - 1
    have hrPrevSucc : rPrev + 1 = YoungCell.row u := by
      simpa [rPrev] using Nat.sub_add_cancel (show 1 ≤ YoungCell.row u by omega)
    have hrowMono := youngRow_succ_le lam rPrev
    rw [hrPrevSucc] at hrowMono
    have hcolAbove : YoungCell.col u < youngRow lam rPrev :=
      lt_of_lt_of_le huBox hrowMono
    let v := youngCellOfNat lam rPrev (YoungCell.col u) hcolAbove
    have hvRow : YoungCell.row v = rPrev :=
      youngCellOfNat_row lam rPrev (YoungCell.col u) hcolAbove
    have hvCol : YoungCell.col v = YoungCell.col u :=
      youngCellOfNat_col lam rPrev (YoungCell.col u) hcolAbove
    have hstrict : T.entry v < T.entry u := by
      apply T.col_strict hvCol
      rw [hvRow, ← hrPrevSucc]
      omega
    have hstrictNat : (T.entry v : Nat) < (T.entry u : Nat) := hstrict
    have huNat : (T.entry u : Nat) = 0 := congrArg Fin.val huEntry
    omega
  have hcol : YoungCell.col u = 0 := by
    by_contra hne
    have hcpos : 0 < YoungCell.col u := Nat.pos_of_ne_zero hne
    let cPrev := YoungCell.col u - 1
    have hcPrevSucc : cPrev + 1 = YoungCell.col u := by
      simpa [cPrev] using Nat.sub_add_cancel (show 1 ≤ YoungCell.col u by omega)
    have hcolLeft : cPrev < youngRow lam (YoungCell.row u) := by
      omega
    let v := youngCellOfNat lam (YoungCell.row u) cPrev hcolLeft
    have hvRow : YoungCell.row v = YoungCell.row u :=
      youngCellOfNat_row lam (YoungCell.row u) cPrev hcolLeft
    have hvCol : YoungCell.col v = cPrev :=
      youngCellOfNat_col lam (YoungCell.row u) cPrev hcolLeft
    have hstrict : T.entry v < T.entry u := by
      apply T.row_strict hvRow
      rw [hvCol, ← hcPrevSucc]
      omega
    have hstrictNat : (T.entry v : Nat) < (T.entry u : Nat) := hstrict
    have huNat : (T.entry u : Nat) = 0 := congrArg Fin.val huEntry
    omega
  simpa [u] using And.intro hrow hcol

/-- The first tableau entry has content zero. -/
theorem entryContent_zero {n : Nat}
    {lam : YoungDiagram (n + 1)} (T : StandardYoungTableau lam) :
    entryContent T (0 : Fin (n + 1)) = 0 := by
  rcases cellOfEntry_zero_row_col T with ⟨hrow, hcol⟩
  simp [entryContent, YoungCell.content, hrow, hcol]

/-- The zeroth Jucys--Murphy coefficient function vanishes. -/
theorem s05_jucysMurphyElement_zero {n : Nat}
    (g : Perm (Fin (n + 1))) :
    s05_jucysMurphyElement (0 : Fin (n + 1)) g = 0 := by
  simp [s05_jucysMurphyElement]

/-- The represented zeroth Jucys--Murphy element is the zero operator. -/
theorem represented_jucysMurphy_zero {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) (f : TableauSpace lam) :
    (∑ g : Perm (Fin (n + 1)),
      s05_jucysMurphyElement (0 : Fin (n + 1)) g •
        action.rep.rho g f) = 0 := by
  apply Finset.sum_eq_zero
  intro g _hg
  rw [s05_jucysMurphyElement_zero]
  exact zero_smul Real (action.rep.rho g f)

/-- The zeroth content operator is the zero operator. -/
theorem jucysMurphyDiagonalOperator_zero {n : Nat}
    {lam : YoungDiagram (n + 1)} (f : TableauSpace lam) :
    jucysMurphyDiagonalOperator (0 : Fin (n + 1)) f = 0 := by
  funext T
  simp [jucysMurphyDiagonalOperator, entryContent_zero]

/-- Every represented Jucys--Murphy element is the corresponding diagonal
content operator. -/
theorem represented_jucysMurphy_eq_diagonal {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (a : Fin (n + 1)) (f : TableauSpace lam) :
    (∑ g : Perm (Fin (n + 1)),
      s05_jucysMurphyElement a g • action.rep.rho g f) =
        jucysMurphyDiagonalOperator a f := by
  induction a using Fin.induction generalizing f with
  | zero =>
      rw [represented_jucysMurphy_zero action f,
        jucysMurphyDiagonalOperator_zero f]
  | succ a ih =>
      rw [represented_jucysMurphy_succ_recurrence action a f]
      rw [ih (action.rep.rho (s05_adjacentTransposition a) f)]
      rw [action.rho_adjacent a
        (jucysMurphyDiagonalOperator a.castSucc
          (action.rep.rho (s05_adjacentTransposition a) f))]
      rw [action.rho_adjacent a f]
      exact youngAdjacent_content_succ_recurrence a f

/-- The internally constructed faithful Section 5.2 content-action data. -/
theorem internalJucysMurphyContentActionData {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) :
    JucysMurphyContentActionData action where
  rho_content := represented_jucysMurphy_eq_diagonal action

/-- Section 5.2's faithful content-action interface is inhabited for every
concrete Young orthogonal action. -/
theorem jucysMurphyContentActionData_nonempty {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam) :
    Nonempty (JucysMurphyContentActionData action) :=
  ⟨internalJucysMurphyContentActionData action⟩

/-- Every nonempty Young diagram has a removable row. -/
theorem exists_removableRow_of_positive_size {n : Nat}
    (lam : YoungDiagram (n + 1)) :
    ∃ r : Nat, IsRemovableRow lam r := by
  have hrowZero : 0 < youngRow lam 0 := by
    by_contra hnot
    have hz : youngRow lam 0 = 0 := Nat.eq_zero_of_not_pos hnot
    have hzStored : (lam.row (0 : Fin (n + 1)) : Nat) = 0 := by
      simpa [youngRow] using hz
    have hall : ∀ i : Fin (n + 1), (lam.row i : Nat) = 0 := by
      intro i
      have hle := lam.nonincreasing
        (i := (0 : Fin (n + 1))) (j := i) (Nat.zero_le _)
      omega
    have hsum := lam.sum_rows
    simp_rw [hall] at hsum
    simp at hsum
  let r := Nat.findGreatest (fun i => 0 < youngRow lam i) n
  have hrPos : 0 < youngRow lam r := by
    exact Nat.findGreatest_spec (P := fun i => 0 < youngRow lam i)
      (m := 0) (n := n) (by omega) hrowZero
  have hrLe : r ≤ n := Nat.findGreatest_le n
  have hsuccZero : youngRow lam (r + 1) = 0 := by
    by_cases hsuccLe : r + 1 ≤ n
    · have hnotPos : ¬ 0 < youngRow lam (r + 1) :=
        Nat.findGreatest_is_greatest (P := fun i => 0 < youngRow lam i)
          (n := n) (k := r + 1) (by omega) hsuccLe
      omega
    · have houtside : ¬ r + 1 < n + 1 := by omega
      simp [youngRow, houtside]
  refine ⟨r, ?_⟩
  unfold IsRemovableRow
  omega

/-- Every Young diagram has a standard row-increasing, column-increasing
tableau.  The construction recursively deletes a last positive row and inserts
the new maximum in that removable corner. -/
theorem standardYoungTableau_nonempty :
    ∀ (n : Nat) (lam : YoungDiagram n),
      Nonempty (StandardYoungTableau lam) := by
  intro n
  induction n with
  | zero =>
      intro lam
      exact ⟨
        { entry := fun u => Fin.elim0 u.1.1
          bijective := by
            constructor
            · intro u
              exact Fin.elim0 u.1.1
            · intro a
              exact Fin.elim0 a
          row_strict := by
            intro u
            exact Fin.elim0 u.1.1
          col_strict := by
            intro u
            exact Fin.elim0 u.1.1 }⟩
  | succ n ih =>
      intro lam
      rcases exists_removableRow_of_positive_size lam with ⟨r, hr⟩
      let mu := deleteRemovableRowDiagram lam r hr
      let S : StandardYoungTableau mu := Classical.choice (ih mu)
      exact ⟨insertMaxAsStandardYoungTableauOfOneBoxChildRow
        (deleteRemovableRowDiagram_isOneBoxChild lam hr)
        (row_form_deleteRemovableRowDiagram lam hr) S⟩

/-- Tableau-count dimensions are strictly positive for every Young diagram. -/
theorem tableauDim_pos_all {n : Nat} (lam : YoungDiagram n) :
    0 < tableauDim lam := by
  exact tableauDim_pos_of_tableau
    (Classical.choice (standardYoungTableau_nonempty n lam))

end DictatorshipTesting
