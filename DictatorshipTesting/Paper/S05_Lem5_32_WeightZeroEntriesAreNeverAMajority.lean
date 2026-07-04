import DictatorshipTesting.Paper.S05_Lem5_15_TwoBoxDimensionRecursion

/-!
Paper statement: Lemma 5.32 (`lem:z-bound-app`)
Title in paper: Weight-zero entries are never a majority.

Status: finite Young-diagram certificate proved below, modulo the two-strip
dimension recursion input.
-/

/-!
# Finite induction input for Lemma 5.32

The paper proves this by induction on `m`, using the horizontal two-strip
recurrence, the dimension recursion, and two special families of diagrams.

This file is the intended home for that proof.  It contains both the detailed
finite induction and the old theorem name `L5_4_ZBoundApp`, so downstream code
does not need a separate wrapper module.
-/

namespace DictatorshipTesting

/-- A diagram has a horizontal two-strip child that is the one-row diagram.  This
is the exact obstruction to applying the induction hypothesis uniformly to all
horizontal children in the proof of the `zEven` bound. -/
def HasOneRowHorizontalChild (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  ∃ mu ∈ horizontalTwoStripChildrenEven m lam, IsOneRow mu

/-- Row predicate for the exceptional two-row shape `(2m-2, 2)`. -/
def IsTwoRowTwoException (m : ℕ) (lam : YoungDiagram (2 * m)) : Prop :=
  youngRow lam 0 = 2 * m - 2 ∧ youngRow lam 1 = 2

/-- Specht dimensions are nonnegative in the concrete hook-length model. -/
theorem youngDim_nonneg {n : ℕ} (lam : YoungDiagram n) :
    0 ≤ youngDim lam := by
  unfold youngDim
  exact_mod_cast Nat.zero_le (youngDimNat lam)

/-- The zero-weight count is nonnegative.  This is the easy positivity part of
the finite induction for Lemma 5.32. -/
theorem zEven_nonneg (m : ℕ) (lam : YoungDiagram (2 * m)) :
    0 ≤ zEven m lam := by
  induction m with
  | zero =>
      simp [zEven]
  | succ m ih =>
      simp [zEven, Finset.sum_nonneg, ih]

/-- The canonical one-row Young diagram. -/
def oneRowDiagram (n : ℕ) : YoungDiagram n where
  row := fun i =>
    if (i : ℕ) = 0 then ⟨n, Nat.lt_succ_self n⟩ else ⟨0, Nat.succ_pos n⟩
  nonincreasing := by
    intro i j hij
    by_cases hj : (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by omega
      simp [hi, hj]
    · simp [hj]
  sum_rows := by
    classical
    by_cases hn : n = 0
    · subst n
      simp
    · let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      rw [Finset.sum_eq_single i0]
      · simp [i0]
      · intro b _hb hba
        have hb0 : (b : ℕ) ≠ 0 := by
          intro hb0
          apply hba
          ext
          simp [i0, hb0]
        simp [hb0]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i0))

/-- The canonical one-row diagram satisfies the one-row predicate. -/
theorem isOneRow_oneRowDiagram (n : ℕ) :
    IsOneRow (oneRowDiagram n) := by
  unfold IsOneRow youngRow oneRowDiagram
  by_cases hn : 0 < n
  · simp [hn]
  · have hzero : n = 0 := by omega
    subst n
    simp

/-- The canonical two-row Young diagram with row lengths `(a,b)`.  The
hypotheses say this is a partition of `n` with two represented rows. -/
def twoRowDiagram (n a b : ℕ) (hn : 2 ≤ n)
    (hab : a + b = n) (hge : b ≤ a) : YoungDiagram n where
  row := fun i =>
    if (i : ℕ) = 0 then ⟨a, by omega⟩
    else if (i : ℕ) = 1 then ⟨b, by omega⟩
    else ⟨0, Nat.succ_pos n⟩
  nonincreasing := by
    intro i j hij
    by_cases hj0 : (j : ℕ) = 0
    · have hi0 : (i : ℕ) = 0 := by omega
      simp [hi0, hj0]
    · by_cases hj1 : (j : ℕ) = 1
      · by_cases hi0 : (i : ℕ) = 0
        · simp [hi0, hj1, hge]
        · have hi1 : (i : ℕ) = 1 := by omega
          simp [hi1, hj1]
      · simp [hj0, hj1]
  sum_rows := by
    classical
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let tail0 : Finset (Fin n) :=
      Finset.erase (Finset.univ : Finset (Fin n)) i0
    let tail1 : Finset (Fin n) := Finset.erase tail0 i1
    have hne10 : Not (i1 = i0) := by
      intro h
      have hv : (i1 : ℕ) = (i0 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [i0, i1] at hv
    have hi1_tail0 : i1 ∈ tail0 := by
      dsimp [tail0]
      exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
    have htail1_zero :
        tail1.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx_erase1 := Finset.mem_erase.mp hx
      have hxne1 : Not (x = i1) := hx_erase1.1
      have hx_tail0 := hx_erase1.2
      have hx_erase0 := Finset.mem_erase.mp hx_tail0
      have hxne0 : Not (x = i0) := hx_erase0.1
      have hx0 : (x : ℕ) ≠ 0 := by
        intro h
        apply hxne0
        ext
        simp [i0, h]
      have hx1 : (x : ℕ) ≠ 1 := by
        intro h
        apply hxne1
        ext
        simp [i1, h]
      simp [hx0, hx1]
    have hsum0 :
        ((if (i0 : ℕ) = 0 then ⟨a, by omega⟩
          else if (i0 : ℕ) = 1 then ⟨b, by omega⟩
          else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ) +
            tail0.sum
              (fun x : Fin n =>
                ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                  else if (x : ℕ) = 1 then ⟨b, by omega⟩
                  else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) =
          Finset.univ.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) := by
      simpa [tail0] using
        Finset.add_sum_erase
          (Finset.univ : Finset (Fin n))
          (fun x : Fin n =>
            ((if (x : ℕ) = 0 then ⟨a, by omega⟩
              else if (x : ℕ) = 1 then ⟨b, by omega⟩
              else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ))
          (Finset.mem_univ i0)
    have hsum1 :
        ((if (i1 : ℕ) = 0 then ⟨a, by omega⟩
          else if (i1 : ℕ) = 1 then ⟨b, by omega⟩
          else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ) +
            tail1.sum
              (fun x : Fin n =>
                ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                  else if (x : ℕ) = 1 then ⟨b, by omega⟩
                  else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) =
          tail0.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) := by
      simpa [tail1] using
        Finset.add_sum_erase tail0
          (fun x : Fin n =>
            ((if (x : ℕ) = 0 then ⟨a, by omega⟩
              else if (x : ℕ) = 1 then ⟨b, by omega⟩
              else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ))
          hi1_tail0
    rw [← hsum0, ← hsum1, htail1_zero]
    simp [i0, i1, hab]

/-- Row formula for the canonical two-row diagram. -/
theorem youngRow_twoRowDiagram (n a b : ℕ) (hn : 2 ≤ n)
    (hab : a + b = n) (hge : b ≤ a) (i : ℕ) :
    youngRow (twoRowDiagram n a b hn hab hge) i =
      if i = 0 then a else if i = 1 then b else 0 := by
  unfold youngRow twoRowDiagram
  by_cases hi : i < n
  · by_cases h0 : i = 0
    · have hn0 : n ≠ 0 := by omega
      simp [h0, hn0]
    · by_cases h1 : i = 1
      · have hnle : ¬ n ≤ 1 := by omega
        simp [h1, hnle]
      · simp [h0, h1]
  · by_cases h0 : i = 0
    · omega
    · by_cases h1 : i = 1
      · omega
      · simp [hi, h0, h1]

/-- The standard shape `(2m-1, 1)` as a canonical two-row diagram. -/
def standardDiagramEven (m : ℕ) (hm : 1 ≤ m) : YoungDiagram (2 * m) :=
  twoRowDiagram (2 * m) (2 * m - 1) 1 (by omega) (by omega) (by omega)

/-- The two-row exception `(2m-2, 2)` as a canonical two-row diagram. -/
def twoRowTwoDiagramEven (m : ℕ) (hm : 2 ≤ m) : YoungDiagram (2 * m) :=
  twoRowDiagram (2 * m) (2 * m - 2) 2 (by omega) (by omega) (by omega)

/-- The canonical standard diagram satisfies the standard predicate. -/
theorem isStandard_standardDiagramEven (m : ℕ) (hm : 1 ≤ m) :
    IsStandard (standardDiagramEven m hm) := by
  unfold standardDiagramEven IsStandard
  constructor
  · omega
  constructor
  · simp [youngRow_twoRowDiagram]
  · simp [youngRow_twoRowDiagram]

/-- The canonical two-row exception satisfies its predicate. -/
theorem isTwoRowTwoException_twoRowTwoDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsTwoRowTwoException m (twoRowTwoDiagramEven m hm) := by
  unfold twoRowTwoDiagramEven IsTwoRowTwoException
  constructor
  · simp [youngRow_twoRowDiagram]
  · simp [youngRow_twoRowDiagram]

/-- Every row length is bounded by the total number of boxes. -/
theorem youngRow_le_size {n : ℕ} (lam : YoungDiagram n) (i : ℕ) :
    youngRow lam i ≤ n := by
  unfold youngRow
  split
  · exact Nat.le_of_lt_succ (lam.row ⟨i, ‹i < n›⟩).isLt
  · omega

/-- Extensionality for the concrete row-vector model of Young diagrams. -/
theorem youngDiagram_ext {n : ℕ} {lam mu : YoungDiagram n}
    (hrow : ∀ i : ℕ, youngRow lam i = youngRow mu i) :
    lam = mu := by
  cases lam with
  | mk lamRow lamNoninc lamSum =>
      cases mu with
      | mk muRow muNoninc muSum =>
          have hrows : lamRow = muRow := by
            funext i
            have hi := hrow i
            unfold youngRow at hi
            simp [i.isLt] at hi
            exact Fin.ext hi
          subst hrows
          simp

/-- The canonical two-row diagram is independent of its proof arguments. -/
theorem twoRowDiagram_proof_irrel (n a b : ℕ)
    (hn₁ hn₂ : 2 ≤ n) (hab₁ hab₂ : a + b = n)
    (hge₁ hge₂ : b ≤ a) :
    twoRowDiagram n a b hn₁ hab₁ hge₁ =
      twoRowDiagram n a b hn₂ hab₂ hge₂ := by
  apply youngDiagram_ext
  intro i
  simp [youngRow_twoRowDiagram]

/-- The canonical standard diagram is independent of its proof argument. -/
theorem standardDiagramEven_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 1 ≤ m) :
    standardDiagramEven m hm₁ = standardDiagramEven m hm₂ := by
  unfold standardDiagramEven
  exact twoRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _

/-- Row formula for the canonical one-row diagram. -/
theorem youngRow_oneRowDiagram (n i : ℕ) :
    youngRow (oneRowDiagram n) i = if i = 0 then n else 0 := by
  unfold youngRow oneRowDiagram
  by_cases hi : i < n
  · by_cases h0 : i = 0
    · have hn0 : n ≠ 0 := by omega
      simp [h0, hn0]
    · simp [hi, h0]
  · by_cases h0 : i = 0
    · subst i
      have hn : n = 0 := by omega
      simp [hn]
    · simp [hi, h0]

/-- In a one-row Young diagram, every row after the first is zero. -/
theorem youngRow_eq_zero_of_isOneRow {n : ℕ}
    (mu : YoungDiagram n) (hone : IsOneRow mu) {i : ℕ} (hi : 1 ≤ i) :
    youngRow mu i = 0 := by
  classical
  by_cases hin : i < n
  · have hnpos : 0 < n := by omega
    let i0 : Fin n := Fin.mk 0 hnpos
    let ii : Fin n := Fin.mk i hin
    have hne : Not (ii = i0) := by
      intro h
      have hv : (ii : ℕ) = (i0 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [ii, i0] at hv
      omega
    have hrow0 : (mu.row i0 : ℕ) = n := by
      unfold IsOneRow youngRow at hone
      simp [hnpos] at hone
      exact hone
    let tail : Finset (Fin n) :=
      Finset.erase (Finset.univ : Finset (Fin n)) i0
    have hsum_erase :
        (mu.row i0 : ℕ) + tail.sum (fun x => (mu.row x : ℕ)) = n := by
      have hadd := Finset.add_sum_erase
        (Finset.univ : Finset (Fin n))
        (fun x : Fin n => (mu.row x : ℕ))
        (Finset.mem_univ i0)
      have hsum :
          Finset.univ.sum (fun j : Fin n => (mu.row j : ℕ)) = n :=
        mu.sum_rows
      simpa [tail, hsum] using hadd
    have hii_tail : ii ∈ tail := by
      dsimp [tail]
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ ii⟩
    have hii_le_tail :
        (mu.row ii : ℕ) ≤ tail.sum (fun x => (mu.row x : ℕ)) := by
      exact
        Finset.single_le_sum
          (s := tail) (f := fun x : Fin n => (mu.row x : ℕ))
          (fun x _hx => Nat.zero_le (mu.row x : ℕ))
          hii_tail
    have hii_zero : (mu.row ii : ℕ) = 0 := by
      omega
    unfold youngRow
    simp [ii, hin, hii_zero]
  · unfold youngRow
    simp [hin]

/-- A one-row diagram is equal to the canonical one-row diagram. -/
theorem eq_oneRowDiagram_of_isOneRow {n : ℕ}
    (mu : YoungDiagram n) (hone : IsOneRow mu) :
    mu = oneRowDiagram n := by
  apply youngDiagram_ext
  intro i
  rw [youngRow_oneRowDiagram]
  by_cases h0 : i = 0
  · subst i
    exact hone
  · simp [h0, youngRow_eq_zero_of_isOneRow mu hone (by omega : 1 ≤ i)]

/-- The canonical one-row child is a horizontal two-strip child of a canonical
one-row parent. -/
theorem oneRowDiagram_horizontalChild (m : ℕ) (hm : 1 ≤ m) :
    IsHorizontalTwoStripChild (oneRowDiagram (2 * m))
      (oneRowDiagram (2 * (m - 1))) := by
  constructor
  · omega
  constructor
  · intro i
    rw [youngRow_oneRowDiagram, youngRow_oneRowDiagram]
    by_cases h0 : (i : ℕ) = 0
    · simp [h0]
    · simp [h0]
  · intro i
    rw [youngRow_oneRowDiagram, youngRow_oneRowDiagram]
    simp

/-- Any horizontal child of a one-row diagram is itself one-row. -/
theorem isOneRow_of_horizontalChild_oneRowDiagram
    (m : ℕ) (hm : 1 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip : IsHorizontalTwoStripChild (oneRowDiagram (2 * m)) mu) :
    IsOneRow mu := by
  classical
  by_cases hk : 2 * (m - 1) = 0
  · unfold IsOneRow youngRow
    simp [hk]
  · have hkpos : 0 < 2 * (m - 1) := Nat.pos_of_ne_zero hk
    let i0 : Fin (2 * (m - 1)) := Fin.mk 0 hkpos
    have hsum_single :
        Finset.univ.sum (fun j : Fin (2 * (m - 1)) => (mu.row j : ℕ)) =
          (mu.row i0 : ℕ) := by
      rw [Finset.sum_eq_single i0]
      · intro b _hb hba
        have hbpos : 1 ≤ (b : ℕ) := by
          have hbne0 : (b : ℕ) ≠ 0 := by
            intro hb0
            apply hba
            ext
            simp [i0, hb0]
          omega
        let ib : Fin (2 * m) := Fin.mk (b : ℕ) (by
          have hb_lt := b.isLt
          omega)
        have hsub := hstrip.2.1 ib
        have hparent : youngRow (oneRowDiagram (2 * m)) (b : ℕ) = 0 := by
          rw [youngRow_oneRowDiagram]
          simp [show (b : ℕ) ≠ 0 by omega]
        have hbzero : youngRow mu (b : ℕ) = 0 := by
          simpa [ib, hparent] using hsub
        unfold youngRow at hbzero
        simp [b.isLt] at hbzero
        exact_mod_cast hbzero
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i0))
    have htotal :
        Finset.univ.sum (fun j : Fin (2 * (m - 1)) => (mu.row j : ℕ)) =
          2 * (m - 1) := mu.sum_rows
    have hrow0 : (mu.row i0 : ℕ) = 2 * (m - 1) := by
      omega
    unfold IsOneRow youngRow
    simp [i0, hkpos, hrow0]

/-- Horizontal children of a canonical one-row diagram form the singleton
canonical one-row child. -/
theorem horizontalTwoStripChildrenEven_oneRowDiagram
    (m : ℕ) (hm : 1 ≤ m) :
    horizontalTwoStripChildrenEven m (oneRowDiagram (2 * m)) =
      {oneRowDiagram (2 * (m - 1))} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip : IsHorizontalTwoStripChild (oneRowDiagram (2 * m)) mu :=
      (Finset.mem_filter.mp hmu).2
    exact Finset.mem_singleton.mpr
      (eq_oneRowDiagram_of_isOneRow mu
        (isOneRow_of_horizontalChild_oneRowDiagram m hm mu hstrip))
  · intro hmu
    have hmu_eq : mu = oneRowDiagram (2 * (m - 1)) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold horizontalTwoStripChildrenEven
    simp [oneRowDiagram_horizontalChild m hm]

/-- A one-row diagram has no vertical two-strip child. -/
theorem verticalTwoStripChildrenEven_oneRowDiagram
    (m : ℕ) (hm : 1 ≤ m) :
    verticalTwoStripChildrenEven m (oneRowDiagram (2 * m)) = ∅ := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip : IsVerticalTwoStripChild (oneRowDiagram (2 * m)) mu :=
      (Finset.mem_filter.mp hmu).2
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (oneRowDiagram (2 * m)) 0 = 2 * m := by
      rw [youngRow_oneRowDiagram]
      simp
    have hmu0_le : youngRow mu 0 ≤ 2 * (m - 1) :=
      youngRow_le_size mu 0
    have hle' : 2 * m ≤ youngRow mu 0 + 1 := by
      simpa [i0, hparent] using hle
    omega
  · intro hmu
    simp at hmu

/-- The one-row Specht dimension is one, for even sizes. -/
theorem youngDim_oneRowDiagram_even [TwoStripDimensionBranchingAssumption] (m : ℕ) :
    youngDim (oneRowDiagram (2 * m)) = 1 := by
  induction m with
  | zero =>
      simp [youngDim, youngDimNat, youngCells, oneRowDiagram]
  | succ m ih =>
      cases m with
      | zero =>
          change youngDim (oneRowDiagram 2) = 1
          norm_num [youngDim]
          native_decide
      | succ k =>
          have hm : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hrec :=
            youngDim_twoStrip_branching_input
              (Nat.succ (Nat.succ k)) hm
              (oneRowDiagram (2 * Nat.succ (Nat.succ k)))
          have hh :=
            horizontalTwoStripChildrenEven_oneRowDiagram
              (Nat.succ (Nat.succ k)) (by omega)
          have hv :=
            verticalTwoStripChildrenEven_oneRowDiagram
              (Nat.succ (Nat.succ k)) (by omega)
          rw [hh, hv] at hrec
          rw [Finset.sum_singleton] at hrec
          simp at hrec
          rw [hrec]
          change
            youngDim (oneRowDiagram (2 * (k + 1))) +
                (Finset.empty :
                  Finset (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                  (fun x => youngDim x) =
              1
          have hzero :
              (Finset.empty :
                  Finset (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                    (fun x => youngDim x) = 0 := by
            rfl
          rw [hzero, ih]
          norm_num

/-- The horizontal two-strip recurrence for `zEven`, separated out for the
finite induction. -/
theorem zEven_horizontal_recurrence (m : ℕ) (hm : 1 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    zEven m lam =
      (horizontalTwoStripChildrenEven m lam).sum
        (fun mu => zEven (m - 1) mu) := by
  cases m with
  | zero =>
      omega
  | succ m =>
      simp [zEven]

/-- The one-row shape contributes exactly one zero local character. -/
theorem zEven_oneRowDiagram (m : ℕ) :
    zEven m (oneRowDiagram (2 * m)) = 1 := by
  induction m with
  | zero =>
      simp [zEven]
  | succ m ih =>
      have hchildren :=
        horizontalTwoStripChildrenEven_oneRowDiagram (m + 1) (by omega)
      change
        (horizontalTwoStripChildrenEven (m + 1)
            (oneRowDiagram (2 * (m + 1)))).sum
          (fun mu => zEven m mu) = 1
      rw [hchildren]
      rw [Finset.sum_singleton]
      exact ih

/-- In a one-row Young diagram, the second row is zero. -/
theorem youngRow_one_eq_zero_of_isOneRow {n : ℕ} (hn : 2 ≤ n)
    (mu : YoungDiagram n) (hone : IsOneRow mu) :
    youngRow mu 1 = 0 := by
  classical
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  let i0 : Fin n := Fin.mk 0 h0n
  let i1 : Fin n := Fin.mk 1 h1n
  have hne10 : Not (i1 = i0) := by
    intro h
    have hv : (i1 : ℕ) = (i0 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i0, i1] at hv
  have hrow0 : (mu.row i0 : ℕ) = n := by
    unfold IsOneRow youngRow at hone
    simp [h0n] at hone
    exact hone
  let tail : Finset (Fin n) :=
    Finset.erase (Finset.univ : Finset (Fin n)) i0
  have hsum_erase :
      (mu.row i0 : ℕ) + tail.sum (fun x => (mu.row x : ℕ)) = n := by
    have hadd := Finset.add_sum_erase
      (Finset.univ : Finset (Fin n))
      (fun x : Fin n => (mu.row x : ℕ))
      (Finset.mem_univ i0)
    have hsum :
        Finset.univ.sum (fun i : Fin n => (mu.row i : ℕ)) = n :=
      mu.sum_rows
    simpa [tail, hsum] using hadd
  have hrow1_le_tail :
      (mu.row i1 : ℕ) ≤ tail.sum (fun x => (mu.row x : ℕ)) := by
    exact
      Finset.single_le_sum
        (s := tail) (f := fun x : Fin n => (mu.row x : ℕ))
        (fun x _hx => Nat.zero_le (mu.row x : ℕ))
        (by
          dsimp [tail]
          exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩)
  have hrow1_zero : (mu.row i1 : ℕ) = 0 := by
    omega
  unfold youngRow
  simp [i1, h1n, hrow1_zero]

/-- A one-row horizontal child forces the parent to have no third row. -/
theorem youngRow_two_eq_zero_of_hasOneRowHorizontalChild
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hchild : HasOneRowHorizontalChild m lam) :
    youngRow lam 2 = 0 := by
  classical
  rcases hchild with ⟨mu, hmu, hone⟩
  have hstrip : IsHorizontalTwoStripChild lam mu :=
    (Finset.mem_filter.mp hmu).2
  have hmu1 : youngRow mu 1 = 0 := by
    apply youngRow_one_eq_zero_of_isOneRow
    · omega
    · exact hone
  have hle := hstrip.2.2 (Fin.mk 1 (by omega : 1 < 2 * m))
  have hrow2_le_zero : youngRow lam 2 ≤ 0 := by
    simpa [hmu1] using hle
  omega

/-- A one-row horizontal child forces the first row of the parent to have length
at least `2m - 2`. -/
theorem youngRow_zero_ge_of_hasOneRowHorizontalChild
    (m : ℕ) (hm : 1 ≤ m) (lam : YoungDiagram (2 * m))
    (hchild : HasOneRowHorizontalChild m lam) :
    2 * m - 2 ≤ youngRow lam 0 := by
  classical
  rcases hchild with ⟨mu, hmu, hone⟩
  have hstrip : IsHorizontalTwoStripChild lam mu :=
    (Finset.mem_filter.mp hmu).2
  have hsub := hstrip.2.1 (Fin.mk 0 (by omega : 0 < 2 * m))
  have hsub0 : youngRow mu 0 ≤ youngRow lam 0 := by
    simpa using hsub
  have hmu0 : youngRow mu 0 = 2 * (m - 1) := hone
  have htwo : 2 * (m - 1) = 2 * m - 2 := by omega
  omega

/-- A non-one-row diagram has first row strictly shorter than the full size. -/
theorem youngRow_zero_lt_size_of_not_oneRow {n : ℕ}
    (lam : YoungDiagram n) (hrow : ¬ IsOneRow lam) :
    youngRow lam 0 < n := by
  have hle : youngRow lam 0 ≤ n := youngRow_le_size lam 0
  unfold IsOneRow at hrow
  omega

/-- If a non-one-row diagram has a one-row horizontal child, its first row is
one of the two possible exceptional lengths. -/
theorem youngRow_zero_eq_standard_or_twoRow_length
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hchild : HasOneRowHorizontalChild m lam) :
    youngRow lam 0 = 2 * m - 1 ∨ youngRow lam 0 = 2 * m - 2 := by
  have hge := youngRow_zero_ge_of_hasOneRowHorizontalChild m (by omega) lam hchild
  have hlt := youngRow_zero_lt_size_of_not_oneRow lam hrow
  omega

/-- If row two is zero, every later row is zero. -/
theorem youngRow_eq_zero_of_two_le_of_youngRow_two_eq_zero {n : ℕ}
    (hn : 2 < n) (lam : YoungDiagram n) (h2 : youngRow lam 2 = 0)
    {i : ℕ} (hi : 2 ≤ i) :
    youngRow lam i = 0 := by
  unfold youngRow
  split
  · rename_i hin
    have hrow2 : (lam.row (Fin.mk 2 hn) : ℕ) = 0 := by
      unfold youngRow at h2
      simp [hn] at h2
      exact_mod_cast h2
    have hle := lam.nonincreasing
      (i := Fin.mk 2 hn) (j := Fin.mk i hin) hi
    have hrow_le_zero : (lam.row (Fin.mk i hin) : ℕ) ≤ 0 := by
      simpa [hrow2] using hle
    omega
  · rfl

/-- If row two is zero, the row sum is just the first two rows. -/
theorem youngRow_zero_add_one_eq_size_of_youngRow_two_eq_zero {n : ℕ}
    (hn : 3 ≤ n) (lam : YoungDiagram n) (h2 : youngRow lam 2 = 0) :
    youngRow lam 0 + youngRow lam 1 = n := by
  classical
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  have h2n : 2 < n := by omega
  let i0 : Fin n := Fin.mk 0 h0n
  let i1 : Fin n := Fin.mk 1 h1n
  have hne10 : Not (i1 = i0) := by
    intro h
    have hv : (i1 : ℕ) = (i0 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i0, i1] at hv
  let tail0 : Finset (Fin n) :=
    Finset.erase (Finset.univ : Finset (Fin n)) i0
  let tail1 : Finset (Fin n) := Finset.erase tail0 i1
  have hi1_tail0 : i1 ∈ tail0 := by
    dsimp [tail0]
    exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
  have htail1_zero :
      tail1.sum (fun x => (lam.row x : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx_erase1 := Finset.mem_erase.mp hx
    have hxne1 : Not (x = i1) := hx_erase1.1
    have hx_tail0 := hx_erase1.2
    have hx_erase0 := Finset.mem_erase.mp hx_tail0
    have hxne0 : Not (x = i0) := hx_erase0.1
    have hxge2 : 2 ≤ (x : ℕ) := by
      have hxne0val : (x : ℕ) ≠ 0 := by
        intro h
        apply hxne0
        ext
        simp [i0, h]
      have hxne1val : (x : ℕ) ≠ 1 := by
        intro h
        apply hxne1
        ext
        simp [i1, h]
      omega
    have hzero :=
      youngRow_eq_zero_of_two_le_of_youngRow_two_eq_zero
        h2n lam h2 hxge2
    unfold youngRow at hzero
    simp [x.isLt] at hzero
    exact_mod_cast hzero
  have hsum0 :
      (lam.row i0 : ℕ) + tail0.sum (fun x => (lam.row x : ℕ)) =
        Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) := by
    simpa [tail0] using
      Finset.add_sum_erase
        (Finset.univ : Finset (Fin n))
        (fun x : Fin n => (lam.row x : ℕ))
        (Finset.mem_univ i0)
  have hsum1 :
      (lam.row i1 : ℕ) + tail1.sum (fun x => (lam.row x : ℕ)) =
        tail0.sum (fun x => (lam.row x : ℕ)) := by
    simpa [tail1] using
      Finset.add_sum_erase tail0
        (fun x : Fin n => (lam.row x : ℕ)) hi1_tail0
  have htotal :
      Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) = n :=
    lam.sum_rows
  have hrow0 : youngRow lam 0 = (lam.row i0 : ℕ) := by
    unfold youngRow
    simp [i0, h0n]
  have hrow1 : youngRow lam 1 = (lam.row i1 : ℕ) := by
    unfold youngRow
    simp [i1, h1n]
  omega

/-- If the first two rows already contain all boxes, then all later rows are
zero. -/
theorem youngRow_eq_zero_of_two_le_of_first_two_sum {n : ℕ}
    (hn : 2 ≤ n) (lam : YoungDiagram n)
    (hsum01 : youngRow lam 0 + youngRow lam 1 = n)
    {i : ℕ} (hi : 2 ≤ i) :
    youngRow lam i = 0 := by
  classical
  by_cases hin : i < n
  · have h0n : 0 < n := by omega
    have h1n : 1 < n := by omega
    let i0 : Fin n := Fin.mk 0 h0n
    let i1 : Fin n := Fin.mk 1 h1n
    let ii : Fin n := Fin.mk i hin
    have hne10 : Not (i1 = i0) := by
      intro h
      have hv : (i1 : ℕ) = (i0 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [i0, i1] at hv
    have hne_i0 : Not (ii = i0) := by
      intro h
      have hv : (ii : ℕ) = (i0 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [ii, i0] at hv
      omega
    have hne_i1 : Not (ii = i1) := by
      intro h
      have hv : (ii : ℕ) = (i1 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [ii, i1] at hv
      omega
    let tail0 : Finset (Fin n) :=
      Finset.erase (Finset.univ : Finset (Fin n)) i0
    let tail1 : Finset (Fin n) := Finset.erase tail0 i1
    have hi1_tail0 : i1 ∈ tail0 := by
      dsimp [tail0]
      exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
    have hii_tail1 : ii ∈ tail1 := by
      dsimp [tail1, tail0]
      exact Finset.mem_erase.mpr
        ⟨hne_i1, Finset.mem_erase.mpr ⟨hne_i0, Finset.mem_univ ii⟩⟩
    have hsum0 :
        (lam.row i0 : ℕ) + tail0.sum (fun x => (lam.row x : ℕ)) =
          Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) := by
      simpa [tail0] using
        Finset.add_sum_erase
          (Finset.univ : Finset (Fin n))
          (fun x : Fin n => (lam.row x : ℕ))
          (Finset.mem_univ i0)
    have hsum1 :
        (lam.row i1 : ℕ) + tail1.sum (fun x => (lam.row x : ℕ)) =
          tail0.sum (fun x => (lam.row x : ℕ)) := by
      simpa [tail1] using
        Finset.add_sum_erase tail0
          (fun x : Fin n => (lam.row x : ℕ)) hi1_tail0
    have htotal :
        Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) = n :=
      lam.sum_rows
    have hrow0 : youngRow lam 0 = (lam.row i0 : ℕ) := by
      unfold youngRow
      simp [i0, h0n]
    have hrow1 : youngRow lam 1 = (lam.row i1 : ℕ) := by
      unfold youngRow
      simp [i1, h1n]
    have htail_zero : tail1.sum (fun x => (lam.row x : ℕ)) = 0 := by
      omega
    have hii_le_tail :
        (lam.row ii : ℕ) ≤ tail1.sum (fun x => (lam.row x : ℕ)) := by
      exact
        Finset.single_le_sum
          (s := tail1) (f := fun x : Fin n => (lam.row x : ℕ))
          (fun x _hx => Nat.zero_le (lam.row x : ℕ))
          hii_tail1
    have hii_zero : (lam.row ii : ℕ) = 0 := by
      omega
    unfold youngRow
    simp [ii, hin, hii_zero]
  · unfold youngRow
    simp [hin]

/-- If every row from the third row onward is zero, then the first two rows
sum to the size of the diagram. -/
theorem youngRow_zero_add_one_eq_size_of_tail_zero {n : ℕ}
    (hn : 2 ≤ n) (lam : YoungDiagram n)
    (htail : ∀ {i : ℕ}, 2 ≤ i → youngRow lam i = 0) :
    youngRow lam 0 + youngRow lam 1 = n := by
  classical
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  let i0 : Fin n := Fin.mk 0 h0n
  let i1 : Fin n := Fin.mk 1 h1n
  have hne10 : Not (i1 = i0) := by
    intro h
    have hv : (i1 : ℕ) = (i0 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i0, i1] at hv
  let tail0 : Finset (Fin n) :=
    Finset.erase (Finset.univ : Finset (Fin n)) i0
  let tail1 : Finset (Fin n) := Finset.erase tail0 i1
  have hi1_tail0 : i1 ∈ tail0 := by
    dsimp [tail0]
    exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
  have htail1_zero :
      tail1.sum (fun x => (lam.row x : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx_erase1 := Finset.mem_erase.mp hx
    have hxne1 : Not (x = i1) := hx_erase1.1
    have hx_tail0 := hx_erase1.2
    have hx_erase0 := Finset.mem_erase.mp hx_tail0
    have hxne0 : Not (x = i0) := hx_erase0.1
    have hxge2 : 2 ≤ (x : ℕ) := by
      have hxne0val : (x : ℕ) ≠ 0 := by
        intro h
        apply hxne0
        ext
        simp [i0, h]
      have hxne1val : (x : ℕ) ≠ 1 := by
        intro h
        apply hxne1
        ext
        simp [i1, h]
      omega
    have hzero := htail hxge2
    unfold youngRow at hzero
    simp [x.isLt] at hzero
    exact_mod_cast hzero
  have hsum0 :
      (lam.row i0 : ℕ) + tail0.sum (fun x => (lam.row x : ℕ)) =
        Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) := by
    simpa [tail0] using
      Finset.add_sum_erase
        (Finset.univ : Finset (Fin n))
        (fun x : Fin n => (lam.row x : ℕ))
        (Finset.mem_univ i0)
  have hsum1 :
      (lam.row i1 : ℕ) + tail1.sum (fun x => (lam.row x : ℕ)) =
        tail0.sum (fun x => (lam.row x : ℕ)) := by
    simpa [tail1] using
      Finset.add_sum_erase tail0
        (fun x : Fin n => (lam.row x : ℕ)) hi1_tail0
  have htotal :
      Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) = n :=
    lam.sum_rows
  have hrow0 : youngRow lam 0 = (lam.row i0 : ℕ) := by
    unfold youngRow
    simp [i0, h0n]
  have hrow1 : youngRow lam 1 = (lam.row i1 : ℕ) := by
    unfold youngRow
    simp [i1, h1n]
  omega

/-- A diagram whose first two rows are `(a,b)` and exhaust the size is the
canonical two-row diagram. -/
theorem eq_twoRowDiagram_of_rows {n a b : ℕ} (hn : 2 ≤ n)
    (hab : a + b = n) (hge : b ≤ a) (lam : YoungDiagram n)
    (h0 : youngRow lam 0 = a) (h1 : youngRow lam 1 = b) :
    lam = twoRowDiagram n a b hn hab hge := by
  apply youngDiagram_ext
  intro i
  rw [youngRow_twoRowDiagram]
  by_cases hi0 : i = 0
  · subst i
    exact h0
  · by_cases hi1 : i = 1
    · subst i
      simp [h1]
    · have hsum01 : youngRow lam 0 + youngRow lam 1 = n := by
        omega
      have hige2 : 2 ≤ i := by omega
      simp [hi0, hi1,
        youngRow_eq_zero_of_two_le_of_first_two_sum hn lam hsum01 hige2]

/-- A standard diagram is the canonical standard two-row diagram. -/
theorem eq_standardDiagramEven_of_isStandard
    (m : ℕ) (hm : 1 ≤ m) (lam : YoungDiagram (2 * m))
    (hstd : IsStandard lam) :
    lam = standardDiagramEven m hm := by
  rcases hstd with ⟨_hn, h0, h1⟩
  unfold standardDiagramEven
  exact eq_twoRowDiagram_of_rows (by omega) (by omega) (by omega) lam h0 h1

/-- A two-row exception diagram is the canonical two-row exception. -/
theorem eq_twoRowTwoDiagramEven_of_isTwoRowTwoException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (htwo : IsTwoRowTwoException m lam) :
    lam = twoRowTwoDiagramEven m hm := by
  rcases htwo with ⟨h0, h1⟩
  unfold twoRowTwoDiagramEven
  exact eq_twoRowDiagram_of_rows (by omega) (by omega) (by omega) lam h0 h1

/-- Horizontal children of the standard shape are the one-row shape and the
smaller standard shape. -/
theorem horizontalChild_standardDiagramEven_classification
    (m : ℕ) (hm : 2 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsHorizontalTwoStripChild (standardDiagramEven m (by omega)) mu) :
    mu = oneRowDiagram (2 * (m - 1)) ∨
      mu = standardDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (standardDiagramEven m (by omega)) i = 0 := by
        unfold standardDiagramEven
        rw [youngRow_twoRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        simp [hi0, hi1]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum01 :
      youngRow mu 0 + youngRow mu 1 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_eq_size_of_tail_zero
      (by omega : 2 ≤ 2 * (m - 1)) mu htail
  have hmu1_le : youngRow mu 1 ≤ 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (standardDiagramEven m (by omega)) 1 = 1 := by
      exact (isStandard_standardDiagramEven m (by omega)).2.2
    simpa [i1, hparent] using hsub
  have hmu1_cases : youngRow mu 1 = 0 ∨ youngRow mu 1 = 1 := by
    omega
  rcases hmu1_cases with hmu1 | hmu1
  · left
    apply eq_oneRowDiagram_of_isOneRow
    unfold IsOneRow
    omega
  · right
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1

/-- The one-row shape is one horizontal child of the standard shape. -/
theorem oneRowDiagram_horizontalChild_standardDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsHorizontalTwoStripChild (standardDiagramEven m (by omega))
      (oneRowDiagram (2 * (m - 1))) := by
  constructor
  · omega
  constructor
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · simp [hi0]
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0]

/-- The smaller standard shape is the other horizontal child of the standard
shape. -/
theorem standardDiagramEven_horizontalChild_standardDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsHorizontalTwoStripChild (standardDiagramEven m (by omega))
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- Horizontal children of the standard shape, as a concrete Finset. -/
theorem horizontalTwoStripChildrenEven_standardDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    horizontalTwoStripChildrenEven m (standardDiagramEven m (by omega)) =
      {oneRowDiagram (2 * (m - 1)),
        standardDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (standardDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases horizontalChild_standardDiagramEven_classification m hm mu hstrip with
      hone | hstd
    · exact Finset.mem_insert.mpr (Or.inl hone)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hstd))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hone | hstd
    · subst hone
      simp [oneRowDiagram_horizontalChild_standardDiagramEven m hm]
    · subst hstd
      simp [standardDiagramEven_horizontalChild_standardDiagramEven m hm]

/-- The standard shape of size two has no horizontal two-strip child. -/
theorem zEven_standardDiagramEven_one :
    zEven 1 (standardDiagramEven 1 (by omega)) = 0 := by
  classical
  change
    (horizontalTwoStripChildrenEven 1 (standardDiagramEven 1 (by omega))).sum
      (fun mu => zEven 0 mu) = 0
  apply Finset.sum_eq_zero
  intro mu hmu
  exfalso
  have hstrip :
      IsHorizontalTwoStripChild (standardDiagramEven 1 (by omega)) mu :=
    (Finset.mem_filter.mp hmu).2
  let i0 : Fin (2 * 1) := Fin.mk 0 (by omega)
  have hle := hstrip.2.2 i0
  have hparent : youngRow (standardDiagramEven 1 (by omega)) 1 = 1 := by
    exact (isStandard_standardDiagramEven 1 (by omega)).2.2
  have hchild : youngRow mu 0 = 0 := by
    unfold youngRow
    simp
  have hbad : (1 : ℕ) ≤ 0 := by
    simp [i0, hparent, hchild] at hle
  omega

/-- Formula for `zEven` on the canonical standard shape. -/
theorem zEven_standardDiagramEven_formula (m : ℕ) (hm : 1 ≤ m) :
    zEven m (standardDiagramEven m hm) = (m : ℝ) - 1 := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          simpa using zEven_standardDiagramEven_one
      | succ k =>
          have hm2 : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hchildren :=
            horizontalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          change
            (horizontalTwoStripChildrenEven (Nat.succ (Nat.succ k))
                (standardDiagramEven (Nat.succ (Nat.succ k)) hm)).sum
              (fun mu => zEven (Nat.succ k) mu) =
                ((Nat.succ (Nat.succ k) : ℕ) : ℝ) - 1
          rw [hchildren]
          have hne :
              standardDiagramEven (Nat.succ k) (by omega) ≠
                oneRowDiagram (2 * Nat.succ k) := by
            intro h
            have hrow := congrArg (fun yd => youngRow yd 1) h
            have hstd1 :
                youngRow (standardDiagramEven (Nat.succ k) (by omega)) 1 = 1 :=
              (isStandard_standardDiagramEven (Nat.succ k) (by omega)).2.2
            have hone1 :
                youngRow (oneRowDiagram (2 * Nat.succ k)) 1 = 0 := by
              rw [youngRow_oneRowDiagram]
              simp
            omega
          rw [Finset.sum_insert]
          · rw [Finset.sum_singleton]
            change
              zEven (Nat.succ k) (oneRowDiagram (2 * Nat.succ k)) +
                  zEven (Nat.succ k)
                    (standardDiagramEven (Nat.succ k) (by omega)) =
                ((Nat.succ (Nat.succ k) : ℕ) : ℝ) - 1
            rw [zEven_oneRowDiagram]
            have ihstd :=
              ih (by omega : 1 ≤ Nat.succ k)
            rw [ihstd]
            simp [Nat.succ_eq_add_one, Nat.cast_add]
            ac_rfl
          · intro hmem
            rw [Finset.mem_singleton] at hmem
            exact hne hmem.symm

/-- The one-row shape is the vertical child of the standard shape. -/
theorem oneRowDiagram_verticalChild_standardDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsVerticalTwoStripChild (standardDiagramEven m (by omega))
      (oneRowDiagram (2 * (m - 1))) := by
  constructor
  · omega
  constructor
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The standard shape has exactly one vertical child, the one-row shape. -/
theorem verticalTwoStripChildrenEven_standardDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    verticalTwoStripChildrenEven m (standardDiagramEven m (by omega)) =
      {oneRowDiagram (2 * (m - 1))} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (standardDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (standardDiagramEven m (by omega)) 0 = 2 * m - 1 :=
      (isStandard_standardDiagramEven m (by omega)).2.1
    have hmu0_le : youngRow mu 0 ≤ 2 * (m - 1) :=
      youngRow_le_size mu 0
    have hmu0 : youngRow mu 0 = 2 * (m - 1) := by
      have hle' : 2 * m - 1 ≤ youngRow mu 0 + 1 := by
        simpa [i0, hparent] using hle
      omega
    have hone : IsOneRow mu := by
      unfold IsOneRow
      exact hmu0
    exact Finset.mem_singleton.mpr (eq_oneRowDiagram_of_isOneRow mu hone)
  · intro hmu
    have hmu_eq : mu = oneRowDiagram (2 * (m - 1)) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [oneRowDiagram_verticalChild_standardDiagramEven m hm]

/-- Dimension formula for the canonical standard shape. -/
theorem youngDim_standardDiagramEven_formula
    [TwoStripDimensionBranchingAssumption] (m : ℕ) (hm : 1 ≤ m) :
    youngDim (standardDiagramEven m hm) = 2 * (m : ℝ) - 1 := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          have hshape :
              standardDiagramEven 1 hm = standardDiagramEven 1 (by omega) := by
            exact standardDiagramEven_proof_irrel 1 hm (by omega)
          rw [hshape]
          norm_num
          change youngDim (standardDiagramEven 1 (by omega)) = 1
          norm_num [youngDim]
          native_decide +revert
      | succ k =>
          have hm2 : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hrec :=
            youngDim_twoStrip_branching_input
              (Nat.succ (Nat.succ k)) hm2
              (standardDiagramEven (Nat.succ (Nat.succ k)) hm)
          have hh :=
            horizontalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          have hv :=
            verticalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          rw [hh, hv] at hrec
          have hne :
              standardDiagramEven (Nat.succ k) (by omega) ≠
                oneRowDiagram (2 * Nat.succ k) := by
            intro h
            have hrow := congrArg (fun yd => youngRow yd 1) h
            have hstd1 :
                youngRow (standardDiagramEven (Nat.succ k) (by omega)) 1 = 1 :=
              (isStandard_standardDiagramEven (Nat.succ k) (by omega)).2.2
            have hone1 :
                youngRow (oneRowDiagram (2 * Nat.succ k)) 1 = 0 := by
              rw [youngRow_oneRowDiagram]
              simp
            omega
          rw [Finset.sum_insert] at hrec
          · rw [Finset.sum_singleton] at hrec
            rw [Finset.sum_singleton] at hrec
            rw [hrec]
            change
              youngDim (oneRowDiagram (2 * Nat.succ k)) +
                  youngDim (standardDiagramEven (Nat.succ k) (by omega)) +
                youngDim (oneRowDiagram (2 * Nat.succ k)) =
                2 * ((Nat.succ (Nat.succ k) : ℕ) : ℝ) - 1
            rw [youngDim_oneRowDiagram_even]
            rw [ih (by omega : 1 ≤ Nat.succ k)]
            simp [Nat.succ_eq_add_one, Nat.cast_add]
            ring
          · intro hmem
            rw [Finset.mem_singleton] at hmem
            exact hne hmem.symm

/-- Horizontal children of `(2m-2,2)` are one-row, standard, or the smaller
two-row exception. -/
theorem horizontalChild_twoRowTwoDiagramEven_classification
    (m : ℕ) (hm : 3 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsHorizontalTwoStripChild (twoRowTwoDiagramEven m (by omega)) mu) :
    mu = oneRowDiagram (2 * (m - 1)) ∨
      mu = standardDiagramEven (m - 1) (by omega) ∨
        mu = twoRowTwoDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (twoRowTwoDiagramEven m (by omega)) i = 0 := by
        unfold twoRowTwoDiagramEven
        rw [youngRow_twoRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        simp [hi0, hi1]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum01 :
      youngRow mu 0 + youngRow mu 1 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_eq_size_of_tail_zero
      (by omega : 2 ≤ 2 * (m - 1)) mu htail
  have hmu1_le : youngRow mu 1 ≤ 2 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (twoRowTwoDiagramEven m (by omega)) 1 = 2 := by
      exact (isTwoRowTwoException_twoRowTwoDiagramEven m (by omega)).2
    simpa [i1, hparent] using hsub
  have hmu1_cases :
      youngRow mu 1 = 0 ∨ youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 := by
    omega
  rcases hmu1_cases with hmu1 | hmu1_or_two
  · left
    apply eq_oneRowDiagram_of_isOneRow
    unfold IsOneRow
    omega
  rcases hmu1_or_two with hmu1 | hmu1
  · right
    left
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1
  · right
    right
    apply eq_twoRowTwoDiagramEven_of_isTwoRowTwoException (m - 1) (by omega)
    unfold IsTwoRowTwoException
    constructor
    · omega
    · exact hmu1

/-- The one-row child of the two-row exception. -/
theorem oneRowDiagram_horizontalChild_twoRowTwoDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsHorizontalTwoStripChild (twoRowTwoDiagramEven m (by omega))
      (oneRowDiagram (2 * (m - 1))) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowTwoDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · simp [hi0]
  · intro i
    unfold twoRowTwoDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0]

/-- The standard child of the two-row exception. -/
theorem standardDiagramEven_horizontalChild_twoRowTwoDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (twoRowTwoDiagramEven m (by omega))
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowTwoDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowTwoDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The smaller two-row exception child of the two-row exception. -/
theorem twoRowTwoDiagramEven_horizontalChild_twoRowTwoDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (twoRowTwoDiagramEven m (by omega))
      (twoRowTwoDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The horizontal children of `(2,2)` consist only of the one-row diagram
`(2)`. -/
theorem horizontalTwoStripChildrenEven_twoRowTwoDiagramEven_two :
    horizontalTwoStripChildrenEven 2 (twoRowTwoDiagramEven 2 (by omega)) =
      {oneRowDiagram 2} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowTwoDiagramEven 2 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    let i0 : Fin (2 * 2) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (twoRowTwoDiagramEven 2 (by omega)) 1 = 2 := by
      exact (isTwoRowTwoException_twoRowTwoDiagramEven 2 (by omega)).2
    have hrow0_ge : 2 ≤ youngRow mu 0 := by
      simpa [i0, hparent] using hle
    have hrow0_le : youngRow mu 0 ≤ 2 := youngRow_le_size mu 0
    have hone : IsOneRow mu := by
      unfold IsOneRow
      omega
    exact Finset.mem_singleton.mpr (eq_oneRowDiagram_of_isOneRow mu hone)
  · intro hmu
    have hmu_eq : mu = oneRowDiagram 2 := Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold horizontalTwoStripChildrenEven
    simp [oneRowDiagram_horizontalChild_twoRowTwoDiagramEven 2 (by omega)]

/-- Horizontal children of `(2m-2,2)` for `m ≥ 3`, as a concrete Finset. -/
theorem horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    horizontalTwoStripChildrenEven m (twoRowTwoDiagramEven m (by omega)) =
      {oneRowDiagram (2 * (m - 1)),
        standardDiagramEven (m - 1) (by omega),
        twoRowTwoDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowTwoDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases horizontalChild_twoRowTwoDiagramEven_classification m hm mu hstrip with
      hone | hrest
    · exact Finset.mem_insert.mpr (Or.inl hone)
    rcases hrest with hstd | htwo
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl hstd)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr htwo))))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hone | hstd | htwo
    · subst hone
      simp [oneRowDiagram_horizontalChild_twoRowTwoDiagramEven m (by omega)]
    · subst hstd
      simp [standardDiagramEven_horizontalChild_twoRowTwoDiagramEven m hm]
    · subst htwo
      simp [twoRowTwoDiagramEven_horizontalChild_twoRowTwoDiagramEven m hm]

/-- Formula for `zEven` on the base two-row exception `(2,2)`. -/
theorem zEven_twoRowTwoDiagramEven_two :
    zEven 2 (twoRowTwoDiagramEven 2 (by omega)) = 1 := by
  change
    (horizontalTwoStripChildrenEven 2 (twoRowTwoDiagramEven 2 (by omega))).sum
      (fun mu => zEven 1 mu) = 1
  rw [horizontalTwoStripChildrenEven_twoRowTwoDiagramEven_two]
  rw [Finset.sum_singleton]
  simpa using zEven_oneRowDiagram 1

/-- Formula for `zEven` on the canonical two-row exception `(2m-2,2)`. -/
theorem zEven_twoRowTwoDiagramEven_formula
    (m : ℕ) (hm : 2 ≤ m) :
    zEven m (twoRowTwoDiagramEven m hm) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              change
                zEven 2 (twoRowTwoDiagramEven 2 (by omega)) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [zEven_twoRowTwoDiagramEven_two]
              norm_num
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hchildren :=
                horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              change
                (horizontalTwoStripChildrenEven
                    (Nat.succ (Nat.succ (Nat.succ k)))
                    (twoRowTwoDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) hm)).sum
                  (fun mu => zEven (Nat.succ (Nat.succ k)) mu) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hchildren]
              let a : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hca : c ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact (isTwoRowTwoException_twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hcb : c ≠ b := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact (isTwoRowTwoException_twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have ha_not :
                  a ∉ ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_insert, Finset.mem_singleton] at hmem
                rcases hmem with hab | hac
                · exact hba hab.symm
                · exact hca hac.symm
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hcb hmem.symm
              change
                ({a, b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                  (fun mu => zEven (Nat.succ (Nat.succ k)) mu) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                zEven (Nat.succ (Nat.succ k))
                    (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                  (zEven (Nat.succ (Nat.succ k))
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  zEven (Nat.succ (Nat.succ k))
                    (twoRowTwoDiagramEven (Nat.succ (Nat.succ k)) (by omega))) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [zEven_oneRowDiagram]
              rw [zEven_standardDiagramEven_formula]
              have ihtwo := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ihtwo]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- The standard shape is the vertical child of the two-row exception. -/
theorem standardDiagramEven_verticalChild_twoRowTwoDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsVerticalTwoStripChild (twoRowTwoDiagramEven m (by omega))
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowTwoDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowTwoDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The two-row exception has exactly one vertical child: the smaller standard
shape. -/
theorem verticalTwoStripChildrenEven_twoRowTwoDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    verticalTwoStripChildrenEven m (twoRowTwoDiagramEven m (by omega)) =
      {standardDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (twoRowTwoDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * (m - 1)
      · let ib : Fin (2 * m) := Fin.mk i (by omega)
        have hsub := hstrip.2.1 ib
        have hparent : youngRow (twoRowTwoDiagramEven m (by omega)) i = 0 := by
          unfold twoRowTwoDiagramEven
          rw [youngRow_twoRowDiagram]
          have hi0 : i ≠ 0 := by omega
          have hi1 : i ≠ 1 := by omega
          simp [hi0, hi1]
        have hle0 : youngRow mu i ≤ 0 := by
          simpa [ib, hparent] using hsub
        omega
      · unfold youngRow
        simp [hin]
    have hsum01 :
        youngRow mu 0 + youngRow mu 1 = 2 * (m - 1) := by
      exact youngRow_zero_add_one_eq_size_of_tail_zero
        (by omega : 2 ≤ 2 * (m - 1)) mu htail
    have hmu0_ge : 2 * m - 3 ≤ youngRow mu 0 := by
      let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
      have hle := hstrip.2.2 i0
      have hparent : youngRow (twoRowTwoDiagramEven m (by omega)) 0 = 2 * m - 2 :=
        (isTwoRowTwoException_twoRowTwoDiagramEven m (by omega)).1
      have hle' : 2 * m - 2 ≤ youngRow mu 0 + 1 := by
        simpa [i0, hparent] using hle
      omega
    have hmu1_ge : 1 ≤ youngRow mu 1 := by
      let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
      have hle := hstrip.2.2 i1
      have hparent : youngRow (twoRowTwoDiagramEven m (by omega)) 1 = 2 :=
        (isTwoRowTwoException_twoRowTwoDiagramEven m (by omega)).2
      have hle' : 2 ≤ youngRow mu 1 + 1 := by
        simpa [i1, hparent] using hle
      omega
    have hmu1 : youngRow mu 1 = 1 := by
      omega
    have hstd : IsStandard mu := by
      unfold IsStandard
      constructor
      · omega
      constructor
      · omega
      · exact hmu1
    exact Finset.mem_singleton.mpr
      (eq_standardDiagramEven_of_isStandard (m - 1) (by omega) mu hstd)
  · intro hmu
    have hmu_eq : mu = standardDiagramEven (m - 1) (by omega) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [standardDiagramEven_verticalChild_twoRowTwoDiagramEven m hm]

/-- Dimension formula for the canonical two-row exception. -/
theorem youngDim_twoRowTwoDiagramEven_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    youngDim (twoRowTwoDiagramEven m hm) =
      (m : ℝ) * (2 * (m : ℝ) - 3) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              change
                youngDim (twoRowTwoDiagramEven 2 (by omega)) =
                  (2 : ℝ) * (2 * (2 : ℝ) - 3)
              have hnat : youngDimNat (twoRowTwoDiagramEven 2 (by omega)) = 2 := by
                native_decide +revert
              norm_num [youngDim, hnat]
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hrec :=
                youngDim_twoStrip_branching_input
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
                  (twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) hm)
              have hh :=
                horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
              rw [hh, hv] at hrec
              let a : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hca : c ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact (isTwoRowTwoException_twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hcb : c ≠ b := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact (isTwoRowTwoException_twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have ha_not :
                  a ∉ ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_insert, Finset.mem_singleton] at hmem
                rcases hmem with hab | hac
                · exact hba hab.symm
                · exact hca hac.symm
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hcb hmem.symm
              rw [Finset.sum_insert ha_not] at hrec
              rw [Finset.sum_insert hb_not] at hrec
              rw [Finset.sum_singleton] at hrec
              rw [Finset.sum_singleton] at hrec
              dsimp [a, b, c] at hrec
              rw [hrec]
              change
                youngDim (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                    (youngDim
                      (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                    youngDim
                      (twoRowTwoDiagramEven (Nat.succ (Nat.succ k)) (by omega))) +
                  youngDim
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) =
                  ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                    (2 * (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ)) - 3)
              rw [youngDim_oneRowDiagram_even]
              rw [youngDim_standardDiagramEven_formula]
              have ihtwo := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ihtwo]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- Two-strip dimension recursion, as supplied by the branching input. -/
theorem youngDim_twoStrip_recurrence
    [TwoStripDimensionBranchingAssumption] (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    youngDim lam =
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) +
        (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
  exact youngDim_twoStrip_branching_input m hm lam

/-- The horizontal part of the two-strip dimension recursion is bounded by the
full dimension. -/
theorem youngDim_horizontalChildren_sum_le
    [TwoStripDimensionBranchingAssumption] (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m)) :
    (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) ≤
      youngDim lam := by
  have hrec := youngDim_twoStrip_recurrence m hm lam
  have hv_nonneg :
      0 ≤ (verticalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
    exact Finset.sum_nonneg (fun mu _hmu => youngDim_nonneg mu)
  linarith

/-- Base case for the finite `zEven` induction at `m = 1`.

There is only one non-one-row diagram of size two, namely `(1,1)`, and its
horizontal two-strip child set is empty. -/
theorem zEven_le_half_youngDim_m_one
    (lam : YoungDiagram (2 * 1)) (hrow : ¬ IsOneRow lam) :
    zEven 1 lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  classical
  have hrow1pos : 0 < youngRow lam 1 := by
    unfold IsOneRow youngRow at hrow
    simp at hrow
    unfold youngRow
    simp
    have hsum : (lam.row 0 : ℕ) + (lam.row 1 : ℕ) = 2 := by
      simpa using lam.sum_rows
    have h0ne : ¬ (lam.row 0 : ℕ) = 2 := by
      exact hrow
    omega
  have hz : zEven 1 lam = 0 := by
    change (horizontalTwoStripChildrenEven 1 lam).sum
      (fun mu => zEven 0 mu) = 0
    apply Finset.sum_eq_zero
    intro mu hmu
    have hstrip : IsHorizontalTwoStripChild lam mu :=
      (Finset.mem_filter.mp hmu).2
    have hle := hstrip.2.2 (0 : Fin (2 * 1))
    have hmu0 : youngRow mu 0 = 0 := by
      unfold youngRow
      simp
    have hzle : youngRow lam 1 ≤ 0 := by
      simpa [hmu0] using hle
    omega
  rw [hz]
  exact mul_nonneg (by norm_num) (youngDim_nonneg lam)

/-- Classification of the non-one-row diagrams with a one-row horizontal
two-strip child.  In row language they are exactly the standard shape
`(2m-1,1)` and the two-row exception `(2m-2,2)`. -/
theorem hasOneRowHorizontalChild_classification
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hchild : HasOneRowHorizontalChild m lam) :
    IsStandard lam ∨ IsTwoRowTwoException m lam := by
  have hrow2 : youngRow lam 2 = 0 :=
    youngRow_two_eq_zero_of_hasOneRowHorizontalChild m hm lam hchild
  have hsum01 : youngRow lam 0 + youngRow lam 1 = 2 * m :=
    youngRow_zero_add_one_eq_size_of_youngRow_two_eq_zero
      (by omega : 3 ≤ 2 * m) lam hrow2
  rcases youngRow_zero_eq_standard_or_twoRow_length m hm lam hrow hchild with
    hstdlen | htwolen
  · left
    unfold IsStandard
    constructor
    · omega
    constructor
    · exact hstdlen
    · omega
  · right
    unfold IsTwoRowTwoException
    constructor
    · exact htwolen
    · omega

/-- Formula for the weight-zero count on the standard shape `(2m-1,1)`. -/
theorem zEven_standard_shape_formula
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hstd : IsStandard lam) :
    zEven m lam = (m : ℝ) - 1 := by
  rw [eq_standardDiagramEven_of_isStandard m (by omega) lam hstd]
  exact zEven_standardDiagramEven_formula m (by omega)

/-- Hook-length dimension formula for the standard shape `(2m-1,1)`. -/
theorem youngDim_standard_shape_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hstd : IsStandard lam) :
    youngDim lam = 2 * (m : ℝ) - 1 := by
  rw [eq_standardDiagramEven_of_isStandard m (by omega) lam hstd]
  exact youngDim_standardDiagramEven_formula m (by omega)

/-- Formula for the weight-zero count on the two-row exception `(2m-2,2)`. -/
theorem zEven_twoRowTwoException_formula
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (htwo : IsTwoRowTwoException m lam) :
    zEven m lam = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m hm lam htwo]
  exact zEven_twoRowTwoDiagramEven_formula m hm

/-- Hook-length dimension formula for the two-row exception `(2m-2,2)`. -/
theorem youngDim_twoRowTwoException_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (htwo : IsTwoRowTwoException m lam) :
    youngDim lam = (m : ℝ) * (2 * (m : ℝ) - 3) := by
  rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m hm lam htwo]
  exact youngDim_twoRowTwoDiagramEven_formula m hm

/-- Exceptional case for the finite `zEven` induction.

If a non-one-row diagram has a one-row horizontal child, the paper's proof
classifies it as one of the two explicit families `(2m-1,1)` or `(2m-2,2)`
and checks the hook-length formulas directly.  That finite classification and
calculation is isolated here. -/
theorem zEven_le_half_youngDim_of_hasOneRowHorizontalChild
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hchild : HasOneRowHorizontalChild m lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  rcases hasOneRowHorizontalChild_classification m hm lam hrow hchild with
    hstd | htwo
  · rw [zEven_standard_shape_formula m hm lam hstd,
      youngDim_standard_shape_formula m hm lam hstd]
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · rw [zEven_twoRowTwoException_formula m hm lam htwo,
      youngDim_twoRowTwoException_formula m hm lam htwo]
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- Generic induction step for the `zEven` bound, away from the one-row-child
exceptions. -/
theorem zEven_le_half_youngDim_of_noOneRowHorizontalChild
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (ih :
      ∀ mu : YoungDiagram (2 * (m - 1)),
        ¬ IsOneRow mu →
          zEven (m - 1) mu ≤ (1 / 2 : ℝ) * youngDim mu)
    (hno : ¬ HasOneRowHorizontalChild m lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  have hzrec := zEven_horizontal_recurrence m (by omega) lam
  rw [hzrec]
  have hchild_nonrow :
      ∀ mu ∈ horizontalTwoStripChildrenEven m lam, ¬ IsOneRow mu := by
    intro mu hmu hone
    exact hno ⟨mu, hmu, hone⟩
  have hsum_ind :
      (horizontalTwoStripChildrenEven m lam).sum (fun mu => zEven (m - 1) mu) ≤
        (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 2 : ℝ) * youngDim mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    exact ih mu (hchild_nonrow mu hmu)
  have hsum_dim :
      (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 2 : ℝ) * youngDim mu) =
        (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) := by
    rw [Finset.mul_sum]
  have hdim_le :
      (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven m lam).sum (fun mu => youngDim mu) ≤
        (1 / 2 : ℝ) * youngDim lam := by
    exact mul_le_mul_of_nonneg_left
      (youngDim_horizontalChildren_sum_le m hm lam) (by norm_num)
  linarith

/-- Finite Young-diagram induction behind Lemma 5.32. -/
theorem zEven_le_half_youngDim_of_not_oneRow_finite_induction
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m)) (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  induction m with
  | zero =>
      have hone : IsOneRow lam := by
        unfold IsOneRow youngRow
        simp
      exact False.elim (hrow hone)
  | succ m ih =>
      cases m with
      | zero =>
          exact zEven_le_half_youngDim_m_one lam hrow
      | succ m =>
          by_cases hchild : HasOneRowHorizontalChild (Nat.succ (Nat.succ m)) lam
          · exact zEven_le_half_youngDim_of_hasOneRowHorizontalChild
              (Nat.succ (Nat.succ m)) (by omega) lam hrow hchild
          · exact zEven_le_half_youngDim_of_noOneRowHorizontalChild
              (Nat.succ (Nat.succ m)) (by omega) lam ih hchild

/-- Lemma 5.32, `lem:z-bound-app`: weight-zero entries are never a majority.
This preserves the old theorem name `L5_4_ZBoundApp`. -/
theorem L5_4_ZBoundApp [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  exact zEven_le_half_youngDim_of_not_oneRow_finite_induction m lam hrow

/-- The zero-weight count is always bounded by the full Young dimension. -/
theorem zEven_le_youngDim [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    zEven m lam ≤ youngDim lam := by
  by_cases hrow : IsOneRow lam
  · rw [eq_oneRowDiagram_of_isOneRow lam hrow]
    rw [zEven_oneRowDiagram, youngDim_oneRowDiagram_even]
  · have hhalf := zEven_le_half_youngDim_of_not_oneRow_finite_induction m lam hrow
    have hdim := youngDim_nonneg lam
    nlinarith

/-- Lemma 5.32 paper-numbered alias: weight-zero entries are never a majority
outside the one-row block. -/
theorem S05_Lem5_32_weightZeroEntries_never_majority
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * youngDim lam := by
  exact L5_4_ZBoundApp m lam hrow

/-- Lemma 5.32 paper-numbered corollary: the zero-weight count is bounded by
the whole Young dimension. -/
theorem S05_Lem5_32_zEven_le_youngDim
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    zEven m lam ≤ youngDim lam := by
  exact zEven_le_youngDim m lam

/-!
## Tableau-dimension certificate layer

The next theorems are the axiom-free part of the migration from the hook-length
proxy `youngDim` to `tableauDim`, the cardinality of standard Young tableaux.
They prove Lemma 5.32 for `tableauDim` using the tableau-count two-strip
recursion from Lemma 5.15 and explicit finite checks for the two exceptional
families in the `zEven` induction.
-/

noncomputable def emptyOneRowTableau :
    StandardYoungTableau (oneRowDiagram 0) where
  entry := fun u => by exact Fin.elim0 u.1.1
  bijective := by
    constructor
    · intro a _b _h
      exact Fin.elim0 a.1.1
    · intro y
      exact Fin.elim0 y
  row_strict := by
    intro u _v _hrow _hcol
    exact Fin.elim0 u.1.1
  col_strict := by
    intro u _v _hcol _hrow
    exact Fin.elim0 u.1.1

theorem tableauDim_oneRowDiagram_zero :
    tableauDim (oneRowDiagram 0) = 1 := by
  have hcard :
      Fintype.card (StandardYoungTableau (oneRowDiagram 0)) = 1 := by
    classical
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨emptyOneRowTableau, ?_⟩
    intro T
    symm
    apply standardYoungTableau_ext_entry
    intro u
    exact Fin.elim0 u.1.1
  norm_num [tableauDim, tableauDimNat, hcard]

theorem tableauDim_oneRowDiagram_even (m : ℕ) :
    tableauDim (oneRowDiagram (2 * m)) = 1 := by
  induction m with
  | zero =>
      simpa using tableauDim_oneRowDiagram_zero
  | succ m ih =>
      have hrec :=
        tableauDim_twoStripChildrenEven_branching_succ
          m (oneRowDiagram (2 * (m + 1)))
      have hh := horizontalTwoStripChildrenEven_oneRowDiagram
        (m + 1) (by omega)
      have hv := verticalTwoStripChildrenEven_oneRowDiagram
        (m + 1) (by omega)
      rw [hh, hv] at hrec
      rw [Finset.sum_singleton] at hrec
      simp at hrec
      rw [hrec]
      change tableauDim (oneRowDiagram (2 * m)) + 0 = 1
      rw [ih]
      norm_num

theorem horizontalTwoStripChildrenEven_standardDiagramEven_one_tableauBase :
    horizontalTwoStripChildrenEven 1 (standardDiagramEven 1 (by omega)) =
      (Finset.empty : Finset (YoungDiagram (2 * (1 - 1)))) := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnon
  rcases hnon with ⟨mu, hmu⟩
  have hstrip :
      IsHorizontalTwoStripChild (standardDiagramEven 1 (by omega)) mu :=
    (Finset.mem_filter.mp hmu).2
  have hle := hstrip.2.2 (Fin.mk 0 (by omega : 0 < 2 * 1))
  have hparent : youngRow (standardDiagramEven 1 (by omega)) 1 = 1 := by
    exact (isStandard_standardDiagramEven 1 (by omega)).2.2
  have hmu0 : youngRow mu 0 = 0 := by
    unfold youngRow
    simp
  have hbad : (1 : ℕ) ≤ 0 := by
    simp [hparent, hmu0] at hle
  omega

theorem oneRowDiagram_verticalChild_standardDiagramEven_one :
    IsVerticalTwoStripChild
      (standardDiagramEven 1 (by omega)) (oneRowDiagram 0) := by
  constructor
  · omega
  constructor
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold standardDiagramEven
    rw [youngRow_oneRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

theorem verticalTwoStripChildrenEven_standardDiagramEven_one_tableauBase :
    verticalTwoStripChildrenEven 1 (standardDiagramEven 1 (by omega)) =
      {oneRowDiagram 0} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hone : IsOneRow mu := by
      unfold IsOneRow youngRow
      simp
    exact Finset.mem_singleton.mpr (eq_oneRowDiagram_of_isOneRow mu hone)
  · intro hmu
    have hmu_eq : mu = oneRowDiagram 0 := Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [oneRowDiagram_verticalChild_standardDiagramEven_one]

theorem tableauDim_standardDiagramEven_one :
    tableauDim (standardDiagramEven 1 (by omega)) = 1 := by
  have hrec :=
    tableauDim_twoStripChildrenEven_branching_succ
      0 (standardDiagramEven 1 (by omega))
  rw [horizontalTwoStripChildrenEven_standardDiagramEven_one_tableauBase] at hrec
  rw [verticalTwoStripChildrenEven_standardDiagramEven_one_tableauBase] at hrec
  rw [Finset.sum_singleton] at hrec
  have hempty :
      Finset.sum
          (Finset.empty : Finset (YoungDiagram (2 * (1 - 1))))
          (fun mu => tableauDim mu) = 0 := by
    exact Finset.sum_empty
  rw [hempty] at hrec
  simp at hrec
  rw [hrec]
  simp [tableauDim_oneRowDiagram_zero]

theorem tableauDim_standardDiagramEven_lower (m : ℕ) (hm : 1 ≤ m) :
    2 * (m : ℝ) - 2 ≤ tableauDim (standardDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          have hnon := tableauDim_nonneg (standardDiagramEven 1 hm)
          norm_num
          exact hnon
      | succ k =>
          have hm2 : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hrec :=
            tableauDim_twoStripChildrenEven_branching_succ
              (Nat.succ k)
              (standardDiagramEven (Nat.succ (Nat.succ k)) hm)
          have hh :=
            horizontalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          have hv :=
            verticalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          rw [hh, hv] at hrec
          let a : YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)) :=
            oneRowDiagram (2 * (Nat.succ (Nat.succ k) - 1))
          let b : YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)) :=
            standardDiagramEven (Nat.succ (Nat.succ k) - 1) (by omega)
          have hba : b ≠ a := by
            intro h
            have hrow := congrArg (fun yd => youngRow yd 1) h
            have hb1 : youngRow b 1 = 1 := by
              dsimp [b]
              exact
                (isStandard_standardDiagramEven
                  (Nat.succ (Nat.succ k) - 1) (by omega)).2.2
            have ha1 : youngRow a 1 = 0 := by
              dsimp [a]
              rw [youngRow_oneRowDiagram]
              simp
            omega
          have ha_not :
              a ∉ ({b} :
                Finset (YoungDiagram
                  (2 * (Nat.succ (Nat.succ k) - 1)))) := by
            intro hmem
            rw [Finset.mem_singleton] at hmem
            exact hba hmem.symm
          rw [Finset.sum_insert ha_not] at hrec
          rw [Finset.sum_singleton] at hrec
          rw [Finset.sum_singleton] at hrec
          dsimp [a, b] at hrec
          rw [hrec]
          have ihstd := ih (by omega : 1 ≤ Nat.succ k)
          have hone := tableauDim_oneRowDiagram_even (Nat.succ k)
          rw [hone]
          norm_num [Nat.succ_eq_add_one, Nat.cast_add] at ihstd ⊢
          linarith

theorem tableauDim_standard_shape_lower
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hstd : IsStandard lam) :
    2 * (m : ℝ) - 2 ≤ tableauDim lam := by
  rw [eq_standardDiagramEven_of_isStandard m (by omega) lam hstd]
  exact tableauDim_standardDiagramEven_lower m (by omega)

theorem twoRowTwoDiagramEven_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 2 ≤ m) :
    twoRowTwoDiagramEven m hm₁ = twoRowTwoDiagramEven m hm₂ := by
  unfold twoRowTwoDiagramEven
  exact twoRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _

theorem tableauDim_twoRowTwoDiagramEven_two :
    tableauDim (twoRowTwoDiagramEven 2 (by omega)) = 2 := by
  have hrec :=
    tableauDim_twoStripChildrenEven_branching_succ
      1 (twoRowTwoDiagramEven 2 (by omega))
  rw [horizontalTwoStripChildrenEven_twoRowTwoDiagramEven_two] at hrec
  rw [verticalTwoStripChildrenEven_twoRowTwoDiagramEven 2 (by omega)] at hrec
  rw [Finset.sum_singleton] at hrec
  rw [Finset.sum_singleton] at hrec
  rw [hrec]
  change
    tableauDim (oneRowDiagram (2 * 1)) +
        tableauDim (standardDiagramEven 1 (by omega)) = 2
  rw [tableauDim_oneRowDiagram_even 1]
  rw [tableauDim_standardDiagramEven_one]
  norm_num

theorem tableauDim_twoRowTwoDiagramEven_lower
    (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) * ((m : ℝ) - 1) ≤
      tableauDim (twoRowTwoDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              rw [twoRowTwoDiagramEven_proof_irrel 2 hm (by omega)]
              rw [tableauDim_twoRowTwoDiagramEven_two]
              norm_num
          | succ k =>
              have hm3 :
                  3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hrec :=
                tableauDim_twoStripChildrenEven_branching_succ
                  (Nat.succ (Nat.succ k))
                  (twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) hm)
              have hh :=
                horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
              rw [hh, hv] at hrec
              let a :
                  YoungDiagram
                    (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b :
                  YoungDiagram
                    (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c :
                  YoungDiagram
                    (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact
                    (isStandard_standardDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k)) - 1)
                      (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hca : c ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact
                    (isTwoRowTwoException_twoRowTwoDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k)) - 1)
                      (by omega)).2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have hcb : c ≠ b := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hc1 : youngRow c 1 = 2 := by
                  dsimp [c]
                  exact
                    (isTwoRowTwoException_twoRowTwoDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k)) - 1)
                      (by omega)).2
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact
                    (isStandard_standardDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k)) - 1)
                      (by omega)).2.2
                omega
              have ha_not :
                  a ∉ ({b, c} :
                    Finset
                      (YoungDiagram
                        (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_insert, Finset.mem_singleton] at hmem
                rcases hmem with hab | hac
                · exact hba hab.symm
                · exact hca hac.symm
              have hb_not :
                  b ∉ ({c} :
                    Finset
                      (YoungDiagram
                        (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hcb hmem.symm
              rw [Finset.sum_insert ha_not] at hrec
              rw [Finset.sum_insert hb_not] at hrec
              rw [Finset.sum_singleton] at hrec
              rw [Finset.sum_singleton] at hrec
              dsimp [a, b, c] at hrec
              rw [hrec]
              have hone :=
                tableauDim_oneRowDiagram_even (Nat.succ (Nat.succ k))
              have hb_lower :=
                tableauDim_standardDiagramEven_lower
                  (Nat.succ (Nat.succ k)) (by omega)
              have hc_lower :=
                ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [hone]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add] at hb_lower hc_lower ⊢
              nlinarith

theorem tableauDim_twoRowTwoException_lower
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (htwo : IsTwoRowTwoException m lam) :
    (m : ℝ) * ((m : ℝ) - 1) ≤ tableauDim lam := by
  rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m hm lam htwo]
  exact tableauDim_twoRowTwoDiagramEven_lower m hm

theorem zEven_le_half_tableauDim_m_one
    (lam : YoungDiagram (2 * 1)) (hrow : ¬ IsOneRow lam) :
    zEven 1 lam ≤ (1 / 2 : ℝ) * tableauDim lam := by
  classical
  have hrow1pos : 0 < youngRow lam 1 := by
    unfold IsOneRow youngRow at hrow
    simp at hrow
    unfold youngRow
    simp
    have hsum : (lam.row 0 : ℕ) + (lam.row 1 : ℕ) = 2 := by
      simpa using lam.sum_rows
    have h0ne : ¬ (lam.row 0 : ℕ) = 2 := by
      exact hrow
    omega
  have hz : zEven 1 lam = 0 := by
    change (horizontalTwoStripChildrenEven 1 lam).sum
      (fun mu => zEven 0 mu) = 0
    apply Finset.sum_eq_zero
    intro mu hmu
    have hstrip :
        IsHorizontalTwoStripChild lam mu :=
      (Finset.mem_filter.mp hmu).2
    have hle := hstrip.2.2 (0 : Fin (2 * 1))
    have hmu0 : youngRow mu 0 = 0 := by
      unfold youngRow
      simp
    have hzle : youngRow lam 1 ≤ 0 := by
      simpa [hmu0] using hle
    omega
  rw [hz]
  exact mul_nonneg (by norm_num) (tableauDim_nonneg lam)

theorem zEven_le_half_tableauDim_of_hasOneRowHorizontalChild
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hchild : HasOneRowHorizontalChild m lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * tableauDim lam := by
  rcases hasOneRowHorizontalChild_classification m hm lam hrow hchild with
    hstd | htwo
  · rw [zEven_standard_shape_formula m hm lam hstd]
    have hdim := tableauDim_standard_shape_lower m hm lam hstd
    nlinarith
  · rw [zEven_twoRowTwoException_formula m hm lam htwo]
    have hdim := tableauDim_twoRowTwoException_lower m hm lam htwo
    nlinarith

theorem zEven_le_half_tableauDim_of_noOneRowHorizontalChild_succ
    (m : ℕ) (lam : YoungDiagram (2 * (m + 1)))
    (ih :
      ∀ mu : YoungDiagram (2 * m),
        ¬ IsOneRow mu →
          zEven m mu ≤ (1 / 2 : ℝ) * tableauDim mu)
    (hno : ¬ HasOneRowHorizontalChild (m + 1) lam) :
    zEven (m + 1) lam ≤ (1 / 2 : ℝ) * tableauDim lam := by
  have hzrec := zEven_horizontal_recurrence (m + 1) (by omega) lam
  rw [hzrec]
  change
    (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => zEven m mu) ≤
      (1 / 2 : ℝ) * tableauDim lam
  have hchild_nonrow :
      ∀ mu ∈ horizontalTwoStripChildrenEven (m + 1) lam, ¬ IsOneRow mu := by
    intro mu hmu hone
    exact hno ⟨mu, hmu, hone⟩
  have hsum_ind :
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => zEven m mu) ≤
        (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => (1 / 2 : ℝ) * tableauDim mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    exact ih mu (hchild_nonrow mu hmu)
  have hsum_dim :
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => (1 / 2 : ℝ) * tableauDim mu) =
        (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven (m + 1) lam).sum
            (fun mu => tableauDim mu) := by
    rw [Finset.mul_sum]
  have hdim_le :
      (1 / 2 : ℝ) *
          (horizontalTwoStripChildrenEven (m + 1) lam).sum
            (fun mu => tableauDim mu) ≤
        (1 / 2 : ℝ) * tableauDim lam := by
    exact mul_le_mul_of_nonneg_left
      (tableauDim_horizontalChildrenEven_sum_le_succ m lam) (by norm_num)
  linarith

theorem zEven_le_half_tableauDim_of_not_oneRow_finite_induction
    (m : ℕ) (lam : YoungDiagram (2 * m)) (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * tableauDim lam := by
  induction m with
  | zero =>
      have hone : IsOneRow lam := by
        unfold IsOneRow youngRow
        simp
      exact False.elim (hrow hone)
  | succ m ih =>
      cases m with
      | zero =>
          exact zEven_le_half_tableauDim_m_one lam hrow
      | succ m =>
          by_cases hchild :
              HasOneRowHorizontalChild (Nat.succ (Nat.succ m)) lam
          · exact zEven_le_half_tableauDim_of_hasOneRowHorizontalChild
              (Nat.succ (Nat.succ m)) (by omega) lam hrow hchild
          · exact
              zEven_le_half_tableauDim_of_noOneRowHorizontalChild_succ
                (Nat.succ m) lam ih hchild

/-- Lemma 5.32, tableau-dimension version: weight-zero entries are never a
majority outside the one-row block. -/
theorem S05_Lem5_32_tableau_weightZeroEntries_never_majority
    (m : ℕ) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) :
    zEven m lam ≤ (1 / 2 : ℝ) * tableauDim lam := by
  exact zEven_le_half_tableauDim_of_not_oneRow_finite_induction m lam hrow

theorem zEven_le_tableauDim
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    zEven m lam ≤ tableauDim lam := by
  by_cases hrow : IsOneRow lam
  · rw [eq_oneRowDiagram_of_isOneRow lam hrow]
    rw [zEven_oneRowDiagram, tableauDim_oneRowDiagram_even]
  · have hhalf :=
      zEven_le_half_tableauDim_of_not_oneRow_finite_induction m lam hrow
    have hdim := tableauDim_nonneg lam
    nlinarith

end DictatorshipTesting
