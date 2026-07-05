import DictatorshipTesting.Paper.S05_Lem5_32_EvenCertificate
import DictatorshipTesting.Paper.S05_Lem5_15_OneBoxDimensionRecursion

/-!
Paper statement: Lemma 5.34 (`lem:h-odd-app`)
Title in paper: Odd certificate.

Status: finite Young-diagram certificate proved below, modulo the one-box
dimension recursion input and Lemma 5.34.
-/

/-!
# Finite induction input for Lemma 5.36

The intended proof branches once to even diagrams, applies Lemma 5.34 to the
non-exceptional children, and handles the two level-two odd shapes explicitly.

The statement is phrased only in terms of the concrete finite model in
`Defs.lean`, so proving it should not require representation theory.
-/

namespace DictatorshipTesting

/-- A diagram has a one-box child that is one-row. -/
def HasOneRowOneBoxChild (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  ∃ mu ∈ oneBoxChildrenOdd m lam, IsOneRow mu

/-- A diagram has a one-box child that is standard. -/
def HasStandardOneBoxChild (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  ∃ mu ∈ oneBoxChildrenOdd m lam, IsStandard mu

/-- Row predicate for the odd exceptional shape `(2m-1,2)`. -/
def IsOddTwoRowTwoException (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  youngRow lam 0 = 2 * m - 1 ∧ youngRow lam 1 = 2

/-- Row predicate for the odd exceptional shape `(2m-1,1,1)`. -/
def IsOddTwoRowOneOneException (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  youngRow lam 0 = 2 * m - 1 ∧ youngRow lam 1 = 1 ∧ youngRow lam 2 = 1

/-- The two exceptional odd shapes from the paper: `(2m-1,2)` and
`(2m-1,1,1)`. -/
def IsOddHExceptional (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : Prop :=
  IsOddTwoRowTwoException m lam ∨ IsOddTwoRowOneOneException m lam

/-- The first three rows of a Young diagram contain at most all boxes. -/
theorem youngRow_zero_add_one_add_two_le_size {n : ℕ}
    (hn : 3 ≤ n) (lam : YoungDiagram n) :
    youngRow lam 0 + youngRow lam 1 + youngRow lam 2 ≤ n := by
  classical
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  have h2n : 2 < n := by omega
  let i0 : Fin n := Fin.mk 0 h0n
  let i1 : Fin n := Fin.mk 1 h1n
  let i2 : Fin n := Fin.mk 2 h2n
  have hne10 : Not (i1 = i0) := by
    intro h
    have hv : (i1 : ℕ) = (i0 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i0, i1] at hv
  have hne20 : Not (i2 = i0) := by
    intro h
    have hv : (i2 : ℕ) = (i0 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i0, i2] at hv
  have hne21 : Not (i2 = i1) := by
    intro h
    have hv : (i2 : ℕ) = (i1 : ℕ) := by
      simpa using congrArg Fin.val h
    simp [i1, i2] at hv
  let tail0 : Finset (Fin n) :=
    Finset.erase (Finset.univ : Finset (Fin n)) i0
  let tail1 : Finset (Fin n) := Finset.erase tail0 i1
  let tail2 : Finset (Fin n) := Finset.erase tail1 i2
  have hi1_tail0 : i1 ∈ tail0 := by
    dsimp [tail0]
    exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
  have hi2_tail1 : i2 ∈ tail1 := by
    dsimp [tail1, tail0]
    exact Finset.mem_erase.mpr
      ⟨hne21, Finset.mem_erase.mpr ⟨hne20, Finset.mem_univ i2⟩⟩
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
  have hsum2 :
      (lam.row i2 : ℕ) + tail2.sum (fun x => (lam.row x : ℕ)) =
        tail1.sum (fun x : Fin n => (lam.row x : ℕ)) := by
    simpa [tail2] using
      Finset.add_sum_erase tail1
        (fun x : Fin n => (lam.row x : ℕ)) hi2_tail1
  have htotal :
      Finset.univ.sum (fun x : Fin n => (lam.row x : ℕ)) = n :=
    lam.sum_rows
  have hrow0 : youngRow lam 0 = (lam.row i0 : ℕ) := by
    unfold youngRow
    simp [i0, h0n]
  have hrow1 : youngRow lam 1 = (lam.row i1 : ℕ) := by
    unfold youngRow
    simp [i1, h1n]
  have hrow2 : youngRow lam 2 = (lam.row i2 : ℕ) := by
    unfold youngRow
    simp [i2, h2n]
  have htail_nonneg : 0 ≤ tail2.sum (fun x : Fin n => (lam.row x : ℕ)) :=
    Nat.zero_le _
  omega

/-- The third row is no longer than the second row. -/
theorem youngRow_two_le_one {n : ℕ} (hn : 3 ≤ n) (lam : YoungDiagram n) :
    youngRow lam 2 ≤ youngRow lam 1 := by
  have h1lt : 1 < n := by omega
  have h2lt : 2 < n := by omega
  have hle := lam.nonincreasing
    (i := Fin.mk 1 h1lt) (j := Fin.mk 2 h2lt) (by norm_num)
  unfold youngRow
  simp [h1lt, h2lt]
  exact hle

/-- The canonical odd exceptional shape `(2m-1,2)`. -/
def twoRowTwoDiagramOdd (m : ℕ) (hm : 2 ≤ m) : YoungDiagram (2 * m + 1) :=
  twoRowDiagram (2 * m + 1) (2 * m - 1) 2
    (by omega) (by omega) (by omega)

/-- The canonical odd exceptional shape `(2m-1,1,1)`. -/
def twoRowOneOneDiagramOdd (m : ℕ) (hm : 2 ≤ m) :
    YoungDiagram (2 * m + 1) :=
  threeRowDiagram (2 * m + 1) (2 * m - 1) 1 1
    (by omega) (by omega) (by omega) (by omega)

theorem twoRowTwoDiagramOdd_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 2 ≤ m) :
    twoRowTwoDiagramOdd m hm₁ = twoRowTwoDiagramOdd m hm₂ := by
  unfold twoRowTwoDiagramOdd
  exact twoRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _

theorem twoRowOneOneDiagramOdd_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 2 ≤ m) :
    twoRowOneOneDiagramOdd m hm₁ = twoRowOneOneDiagramOdd m hm₂ := by
  unfold twoRowOneOneDiagramOdd
  exact threeRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _ _ _ _

theorem isOddTwoRowTwoException_twoRowTwoDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOddTwoRowTwoException m (twoRowTwoDiagramOdd m hm) := by
  unfold twoRowTwoDiagramOdd IsOddTwoRowTwoException
  constructor
  · simp [youngRow_twoRowDiagram]
  · simp [youngRow_twoRowDiagram]

theorem isOddTwoRowOneOneException_twoRowOneOneDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOddTwoRowOneOneException m (twoRowOneOneDiagramOdd m hm) := by
  unfold twoRowOneOneDiagramOdd IsOddTwoRowOneOneException
  constructor
  · simp [youngRow_threeRowDiagram]
  constructor
  · simp [youngRow_threeRowDiagram]
  · simp [youngRow_threeRowDiagram]

theorem eq_twoRowTwoDiagramOdd_of_isOddTwoRowTwoException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowTwoException m lam) :
    lam = twoRowTwoDiagramOdd m hm := by
  rcases hshape with ⟨h0, h1⟩
  unfold twoRowTwoDiagramOdd
  exact eq_twoRowDiagram_of_rows (by omega) (by omega) (by omega) lam h0 h1

theorem eq_twoRowOneOneDiagramOdd_of_isOddTwoRowOneOneException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowOneOneException m lam) :
    lam = twoRowOneOneDiagramOdd m hm := by
  rcases hshape with ⟨h0, h1, h2⟩
  unfold twoRowOneOneDiagramOdd
  exact
    eq_threeRowDiagram_of_rows
      (n := 2 * m + 1) (a := 2 * m - 1) (b := 1) (c := 1)
      (by omega) (by omega) (by omega) (by omega) lam h0 h1 h2

/-- The standard child of `(2m-1,2)`. -/
theorem standardDiagramEven_oneBoxChild_twoRowTwoDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOneBoxChild (twoRowTwoDiagramOdd m hm)
      (standardDiagramEven m (by omega)) := by
  constructor
  · omega
  · intro i
    unfold twoRowTwoDiagramOdd standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The `(2m-2,2)` child of `(2m-1,2)`. -/
theorem twoRowTwoDiagramEven_oneBoxChild_twoRowTwoDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOneBoxChild (twoRowTwoDiagramOdd m hm)
      (twoRowTwoDiagramEven m hm) := by
  constructor
  · omega
  · intro i
    unfold twoRowTwoDiagramOdd twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The one-box children of `(2m-1,2)`. -/
theorem oneBoxChildrenOdd_twoRowTwoDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    oneBoxChildrenOdd m (twoRowTwoDiagramOdd m hm) =
      {standardDiagramEven m (by omega), twoRowTwoDiagramEven m hm} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hchild : IsOneBoxChild (twoRowTwoDiagramOdd m hm) mu :=
      (Finset.mem_filter.mp hmu).2
    have hsub := hchild.2
    have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * m
      · let ii : Fin (2 * m + 1) := Fin.mk i (by omega)
        have hle := hsub ii
        have hle' :
            youngRow mu i ≤ youngRow (twoRowTwoDiagramOdd m hm) i := by
          simpa [ii] using hle
        have hparent : youngRow (twoRowTwoDiagramOdd m hm) i = 0 := by
          unfold twoRowTwoDiagramOdd
          rw [youngRow_twoRowDiagram]
          have hi0 : i ≠ 0 := by omega
          have hi1 : i ≠ 1 := by omega
          simp [hi0, hi1]
        omega
      · unfold youngRow
        simp [hin]
    have hsum :
        youngRow mu 0 + youngRow mu 1 = 2 * m :=
      youngRow_zero_add_one_eq_size_of_tail_zero (by omega) mu htail
    have hrow0_le : youngRow mu 0 ≤ 2 * m - 1 := by
      let i0 : Fin (2 * m + 1) := Fin.mk 0 (by omega)
      have hle := hsub i0
      have hle' :
          youngRow mu 0 ≤ youngRow (twoRowTwoDiagramOdd m hm) 0 := by
        simpa [i0] using hle
      have hparent : youngRow (twoRowTwoDiagramOdd m hm) 0 = 2 * m - 1 := by
        exact (isOddTwoRowTwoException_twoRowTwoDiagramOdd m hm).1
      omega
    have hrow1_le : youngRow mu 1 ≤ 2 := by
      let i1 : Fin (2 * m + 1) := Fin.mk 1 (by omega)
      have hle := hsub i1
      have hle' :
          youngRow mu 1 ≤ youngRow (twoRowTwoDiagramOdd m hm) 1 := by
        simpa [i1] using hle
      have hparent : youngRow (twoRowTwoDiagramOdd m hm) 1 = 2 := by
        exact (isOddTwoRowTwoException_twoRowTwoDiagramOdd m hm).2
      omega
    have hrow1_ge : 1 ≤ youngRow mu 1 := by omega
    have hcases : youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 := by omega
    rcases hcases with h1 | h2
    · have h0 : youngRow mu 0 = 2 * m - 1 := by omega
      have hstd : IsStandard mu := by
        unfold IsStandard
        exact ⟨by omega, h0, h1⟩
      have hmu_eq := eq_standardDiagramEven_of_isStandard m (by omega) mu hstd
      rw [hmu_eq]
      simp
    · have h0 : youngRow mu 0 = 2 * m - 2 := by omega
      have htwo : IsTwoRowTwoException m mu := by
        unfold IsTwoRowTwoException
        exact ⟨h0, h2⟩
      have hmu_eq := eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m hm mu htwo
      rw [hmu_eq]
      simp
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with hmu | hmu
    · subst hmu
      unfold oneBoxChildrenOdd
      simp [standardDiagramEven_oneBoxChild_twoRowTwoDiagramOdd m hm]
    · subst hmu
      unfold oneBoxChildrenOdd
      simp [twoRowTwoDiagramEven_oneBoxChild_twoRowTwoDiagramOdd m hm]

/-- The standard child of `(2m-1,1,1)`. -/
theorem standardDiagramEven_oneBoxChild_twoRowOneOneDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOneBoxChild (twoRowOneOneDiagramOdd m hm)
      (standardDiagramEven m (by omega)) := by
  constructor
  · omega
  · intro i
    unfold twoRowOneOneDiagramOdd standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- The `(2m-2,1,1)` child of `(2m-1,1,1)`. -/
theorem twoRowOneOneDiagramEven_oneBoxChild_twoRowOneOneDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    IsOneBoxChild (twoRowOneOneDiagramOdd m hm)
      (twoRowOneOneDiagramEven m hm) := by
  constructor
  · omega
  · intro i
    unfold twoRowOneOneDiagramOdd twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- The one-box children of `(2m-1,1,1)`. -/
theorem oneBoxChildrenOdd_twoRowOneOneDiagramOdd
    (m : ℕ) (hm : 2 ≤ m) :
    oneBoxChildrenOdd m (twoRowOneOneDiagramOdd m hm) =
      {standardDiagramEven m (by omega), twoRowOneOneDiagramEven m hm} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hchild : IsOneBoxChild (twoRowOneOneDiagramOdd m hm) mu :=
      (Finset.mem_filter.mp hmu).2
    have hsub := hchild.2
    have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * m
      · let ii : Fin (2 * m + 1) := Fin.mk i (by omega)
        have hle := hsub ii
        have hle' :
            youngRow mu i ≤ youngRow (twoRowOneOneDiagramOdd m hm) i := by
          simpa [ii] using hle
        have hparent : youngRow (twoRowOneOneDiagramOdd m hm) i = 0 := by
          unfold twoRowOneOneDiagramOdd
          rw [youngRow_threeRowDiagram]
          have hi0 : i ≠ 0 := by omega
          have hi1 : i ≠ 1 := by omega
          have hi2 : i ≠ 2 := by omega
          simp [hi0, hi1, hi2]
        omega
      · unfold youngRow
        simp [hin]
    have hsum :
        youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 2 * m :=
      youngRow_zero_add_one_add_two_eq_size_of_tail_zero (by omega) mu htail
    have hrow0_le : youngRow mu 0 ≤ 2 * m - 1 := by
      let i0 : Fin (2 * m + 1) := Fin.mk 0 (by omega)
      have hle := hsub i0
      have hle' :
          youngRow mu 0 ≤ youngRow (twoRowOneOneDiagramOdd m hm) 0 := by
        simpa [i0] using hle
      have hparent : youngRow (twoRowOneOneDiagramOdd m hm) 0 = 2 * m - 1 := by
        exact (isOddTwoRowOneOneException_twoRowOneOneDiagramOdd m hm).1
      omega
    have hrow1_le : youngRow mu 1 ≤ 1 := by
      let i1 : Fin (2 * m + 1) := Fin.mk 1 (by omega)
      have hle := hsub i1
      have hle' :
          youngRow mu 1 ≤ youngRow (twoRowOneOneDiagramOdd m hm) 1 := by
        simpa [i1] using hle
      have hparent : youngRow (twoRowOneOneDiagramOdd m hm) 1 = 1 := by
        exact (isOddTwoRowOneOneException_twoRowOneOneDiagramOdd m hm).2.1
      omega
    have hrow2_le : youngRow mu 2 ≤ 1 := by
      let i2 : Fin (2 * m + 1) := Fin.mk 2 (by omega)
      have hle := hsub i2
      have hle' :
          youngRow mu 2 ≤ youngRow (twoRowOneOneDiagramOdd m hm) 2 := by
        simpa [i2] using hle
      have hparent : youngRow (twoRowOneOneDiagramOdd m hm) 2 = 1 := by
        exact (isOddTwoRowOneOneException_twoRowOneOneDiagramOdd m hm).2.2
      omega
    have hrow21 : youngRow mu 2 ≤ youngRow mu 1 := by
      have h1lt : 1 < 2 * m := by omega
      have h2lt : 2 < 2 * m := by omega
      have hle := mu.nonincreasing
        (i := Fin.mk 1 h1lt)
        (j := Fin.mk 2 h2lt) (by norm_num)
      unfold youngRow
      simp [h1lt, h2lt]
      exact hle
    have hrow0_ge : 2 * m - 2 ≤ youngRow mu 0 := by omega
    have hcases :
        youngRow mu 0 = 2 * m - 1 ∨ youngRow mu 0 = 2 * m - 2 := by
      omega
    rcases hcases with h0 | h0
    · have h1 : youngRow mu 1 = 1 := by omega
      have h2 : youngRow mu 2 = 0 := by omega
      have hstd : IsStandard mu := by
        unfold IsStandard
        exact ⟨by omega, h0, h1⟩
      have hmu_eq := eq_standardDiagramEven_of_isStandard m (by omega) mu hstd
      rw [hmu_eq]
      simp
    · have h1 : youngRow mu 1 = 1 := by omega
      have h2 : youngRow mu 2 = 1 := by omega
      have htwo : IsTwoRowOneOneException m mu := by
        unfold IsTwoRowOneOneException
        exact ⟨h0, h1, h2⟩
      have hmu_eq := eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException m hm mu htwo
      rw [hmu_eq]
      simp
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with hmu | hmu
    · subst hmu
      unfold oneBoxChildrenOdd
      simp [standardDiagramEven_oneBoxChild_twoRowOneOneDiagramOdd m hm]
    · subst hmu
      unfold oneBoxChildrenOdd
      simp [twoRowOneOneDiagramEven_oneBoxChild_twoRowOneOneDiagramOdd m hm]

/-- Formula for `hOdd` on the canonical odd exception `(2m-1,2)`. -/
theorem hOdd_twoRowTwoDiagramOdd_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    hOdd m (twoRowTwoDiagramOdd m hm) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [hOdd, oneBoxChildrenOdd_twoRowTwoDiagramOdd m hm]
  have hne :
      twoRowTwoDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 1) h
    have htwo : youngRow (twoRowTwoDiagramEven m hm) 1 = 2 :=
      (isTwoRowTwoException_twoRowTwoDiagramEven m hm).2
    have hstd : youngRow (standardDiagramEven m (by omega)) 1 = 1 :=
      (isStandard_standardDiagramEven m (by omega)).2.2
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [hEven_standardDiagramEven_formula]
    rw [hEven_twoRowTwoDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Dimension formula for the canonical odd exception `(2m-1,2)`. -/
theorem youngDim_twoRowTwoDiagramOdd_formula
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    youngDim (twoRowTwoDiagramOdd m hm) =
      (2 * (m : ℝ) + 1) * ((m : ℝ) - 1) := by
  rw [youngDim_oneBox_branching_input m (twoRowTwoDiagramOdd m hm)]
  rw [oneBoxChildrenOdd_twoRowTwoDiagramOdd m hm]
  have hne :
      twoRowTwoDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 1) h
    have htwo : youngRow (twoRowTwoDiagramEven m hm) 1 = 2 :=
      (isTwoRowTwoException_twoRowTwoDiagramEven m hm).2
    have hstd : youngRow (standardDiagramEven m (by omega)) 1 = 1 :=
      (isStandard_standardDiagramEven m (by omega)).2.2
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [youngDim_standardDiagramEven_formula]
    rw [youngDim_twoRowTwoDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Formula for `hOdd` on the canonical odd exception `(2m-1,1,1)`. -/
theorem hOdd_twoRowOneOneDiagramOdd_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    hOdd m (twoRowOneOneDiagramOdd m hm) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [hOdd, oneBoxChildrenOdd_twoRowOneOneDiagramOdd m hm]
  have hne :
      twoRowOneOneDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 2) h
    have htwo : youngRow (twoRowOneOneDiagramEven m hm) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m hm).2.2
    have hstd : youngRow (standardDiagramEven m (by omega)) 2 = 0 := by
      unfold standardDiagramEven
      rw [youngRow_twoRowDiagram]
      simp
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [hEven_standardDiagramEven_formula]
    rw [hEven_twoRowOneOneDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Dimension formula for the canonical odd exception `(2m-1,1,1)`. -/
theorem youngDim_twoRowOneOneDiagramOdd_formula
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    youngDim (twoRowOneOneDiagramOdd m hm) =
      (m : ℝ) * (2 * (m : ℝ) - 1) := by
  rw [youngDim_oneBox_branching_input m (twoRowOneOneDiagramOdd m hm)]
  rw [oneBoxChildrenOdd_twoRowOneOneDiagramOdd m hm]
  have hne :
      twoRowOneOneDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 2) h
    have htwo : youngRow (twoRowOneOneDiagramEven m hm) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m hm).2.2
    have hstd : youngRow (standardDiagramEven m (by omega)) 2 = 0 := by
      unfold standardDiagramEven
      rw [youngRow_twoRowDiagram]
      simp
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [youngDim_standardDiagramEven_formula]
    rw [youngDim_twoRowOneOneDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Exceptional odd case `(2m-1,2)`. -/
theorem hOdd_ge_one_sixth_youngDim_twoRowTwoOddException
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowTwoException m lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  rw [eq_twoRowTwoDiagramOdd_of_isOddTwoRowTwoException m hm lam hshape]
  rw [hOdd_twoRowTwoDiagramOdd_formula m hm]
  rw [youngDim_twoRowTwoDiagramOdd_formula m hm]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Exceptional odd case `(2m-1,1,1)`. -/
theorem hOdd_ge_one_sixth_youngDim_twoRowOneOneOddException
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowOneOneException m lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  rw [eq_twoRowOneOneDiagramOdd_of_isOddTwoRowOneOneException m hm lam hshape]
  rw [hOdd_twoRowOneOneDiagramOdd_formula m hm]
  rw [youngDim_twoRowOneOneDiagramOdd_formula m hm]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- The two exceptional odd-shape checks bundled as a case split. -/
theorem hOdd_ge_one_sixth_youngDim_odd_exceptional
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hex : IsOddHExceptional m lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  rcases hex with h22 | h211
  · exact hOdd_ge_one_sixth_youngDim_twoRowTwoOddException m hm lam h22
  · exact hOdd_ge_one_sixth_youngDim_twoRowOneOneOddException m hm lam h211

/-- If a nontrivial, nonstandard odd diagram has a one-box child outside the
range of the even certificate, then it is one of the two explicit odd
exceptions `(2m-1,2)` or `(2m-1,1,1)`. -/
theorem odd_bad_oneBoxChild_classification
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad : HasOneRowOneBoxChild m lam ∨ HasStandardOneBoxChild m lam) :
    IsOddHExceptional m lam := by
  classical
  rcases hbad with hbad_row | hbad_std
  · rcases hbad_row with ⟨mu, hmu, hone⟩
    have hchild : IsOneBoxChild lam mu := (Finset.mem_filter.mp hmu).2
    have hsub := hchild.2
    have hsub0_raw := hsub (Fin.mk 0 (by omega : 0 < 2 * m + 1))
    have hsub0 : youngRow mu 0 ≤ youngRow lam 0 := by
      simpa using hsub0_raw
    have hmu0 : youngRow mu 0 = 2 * m := hone
    have hlam0 : youngRow lam 0 = 2 * m := by
      have hlt := youngRow_zero_lt_size_of_not_oneRow lam hrow
      omega
    have hsum3 :
        youngRow lam 0 + youngRow lam 1 + youngRow lam 2 ≤ 2 * m + 1 :=
      youngRow_zero_add_one_add_two_le_size (by omega : 3 ≤ 2 * m + 1) lam
    have h21 : youngRow lam 2 ≤ youngRow lam 1 :=
      youngRow_two_le_one (by omega : 3 ≤ 2 * m + 1) lam
    have h1 : youngRow lam 1 = 1 := by
      have h1le : youngRow lam 1 ≤ 1 := by omega
      by_cases h1zero : youngRow lam 1 = 0
      · have h2zero : youngRow lam 2 = 0 := by omega
        have hsum01 :=
          youngRow_zero_add_one_eq_size_of_youngRow_two_eq_zero
            (by omega : 3 ≤ 2 * m + 1) lam h2zero
        omega
      · omega
    have hstd_lam : IsStandard lam := by
      refine ⟨by omega, ?_, h1⟩
      omega
    exact False.elim (hstd hstd_lam)
  · rcases hbad_std with ⟨mu, hmu, hmu_std⟩
    have hchild : IsOneBoxChild lam mu := (Finset.mem_filter.mp hmu).2
    have hsub := hchild.2
    have hsub0_raw := hsub (Fin.mk 0 (by omega : 0 < 2 * m + 1))
    have hsub1_raw := hsub (Fin.mk 1 (by omega : 1 < 2 * m + 1))
    have hsub0 : youngRow mu 0 ≤ youngRow lam 0 := by
      simpa using hsub0_raw
    have hsub1 : youngRow mu 1 ≤ youngRow lam 1 := by
      simpa using hsub1_raw
    rcases hmu_std with ⟨_, hmu0, hmu1⟩
    have h0ge : 2 * m - 1 ≤ youngRow lam 0 := by omega
    have h1ge : 1 ≤ youngRow lam 1 := by omega
    have h0lt : youngRow lam 0 < 2 * m + 1 :=
      youngRow_zero_lt_size_of_not_oneRow lam hrow
    have hsum3 :
        youngRow lam 0 + youngRow lam 1 + youngRow lam 2 ≤ 2 * m + 1 :=
      youngRow_zero_add_one_add_two_le_size (by omega : 3 ≤ 2 * m + 1) lam
    have h21 : youngRow lam 2 ≤ youngRow lam 1 :=
      youngRow_two_le_one (by omega : 3 ≤ 2 * m + 1) lam
    have h0cases :
        youngRow lam 0 = 2 * m ∨ youngRow lam 0 = 2 * m - 1 := by
      omega
    rcases h0cases with h0 | h0
    · have h1 : youngRow lam 1 = 1 := by omega
      have hstd_lam : IsStandard lam := by
        refine ⟨by omega, ?_, h1⟩
        omega
      exact False.elim (hstd hstd_lam)
    · have h1cases : youngRow lam 1 = 2 ∨ youngRow lam 1 = 1 := by
        omega
      rcases h1cases with h1 | h1
      · exact Or.inl ⟨h0, h1⟩
      · have h2 : youngRow lam 2 = 1 := by
          by_cases h2zero : youngRow lam 2 = 0
          · have hsum01 :=
              youngRow_zero_add_one_eq_size_of_youngRow_two_eq_zero
                (by omega : 3 ≤ 2 * m + 1) lam h2zero
            omega
          · omega
        exact Or.inr ⟨h0, h1, h2⟩

/-- Odd high-weight count using actual tableau dimensions in the even
children. -/
noncomputable def hOddTableau (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  (oneBoxChildrenOdd m lam).sum (fun mu => hEvenTableau m mu)

/-- Formula for `hOddTableau` on the canonical odd exception `(2m-1,2)`. -/
theorem hOddTableau_twoRowTwoDiagramOdd_formula
    (m : ℕ) (hm : 2 ≤ m) :
    hOddTableau m (twoRowTwoDiagramOdd m hm) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [hOddTableau, oneBoxChildrenOdd_twoRowTwoDiagramOdd m hm]
  have hne :
      twoRowTwoDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 1) h
    have htwo : youngRow (twoRowTwoDiagramEven m hm) 1 = 2 :=
      (isTwoRowTwoException_twoRowTwoDiagramEven m hm).2
    have hstd : youngRow (standardDiagramEven m (by omega)) 1 = 1 :=
      (isStandard_standardDiagramEven m (by omega)).2.2
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [hEvenTableau_standardDiagramEven_formula]
    rw [hEvenTableau_twoRowTwoDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Tableau-dimension formula for the canonical odd exception `(2m-1,2)`. -/
theorem tableauDim_twoRowTwoDiagramOdd_formula
    (m : ℕ) (hm : 2 ≤ m) :
    tableauDim (twoRowTwoDiagramOdd m hm) =
      (2 * (m : ℝ) + 1) * ((m : ℝ) - 1) := by
  rw [tableauDim_oneBoxChildrenOdd_branching m (twoRowTwoDiagramOdd m hm)]
  rw [oneBoxChildrenOdd_twoRowTwoDiagramOdd m hm]
  have hne :
      twoRowTwoDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 1) h
    have htwo : youngRow (twoRowTwoDiagramEven m hm) 1 = 2 :=
      (isTwoRowTwoException_twoRowTwoDiagramEven m hm).2
    have hstd : youngRow (standardDiagramEven m (by omega)) 1 = 1 :=
      (isStandard_standardDiagramEven m (by omega)).2.2
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [tableauDim_standardDiagramEven_formula]
    rw [tableauDim_twoRowTwoDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Formula for `hOddTableau` on the canonical odd exception `(2m-1,1,1)`. -/
theorem hOddTableau_twoRowOneOneDiagramOdd_formula
    (m : ℕ) (hm : 2 ≤ m) :
    hOddTableau m (twoRowOneOneDiagramOdd m hm) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [hOddTableau, oneBoxChildrenOdd_twoRowOneOneDiagramOdd m hm]
  have hne :
      twoRowOneOneDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 2) h
    have htwo : youngRow (twoRowOneOneDiagramEven m hm) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m hm).2.2
    have hstd : youngRow (standardDiagramEven m (by omega)) 2 = 0 := by
      unfold standardDiagramEven
      rw [youngRow_twoRowDiagram]
      simp
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [hEvenTableau_standardDiagramEven_formula]
    rw [hEvenTableau_twoRowOneOneDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

/-- Tableau-dimension formula for the canonical odd exception
`(2m-1,1,1)`. -/
theorem tableauDim_twoRowOneOneDiagramOdd_formula
    (m : ℕ) (hm : 2 ≤ m) :
    tableauDim (twoRowOneOneDiagramOdd m hm) =
      (m : ℝ) * (2 * (m : ℝ) - 1) := by
  rw [tableauDim_oneBoxChildrenOdd_branching m (twoRowOneOneDiagramOdd m hm)]
  rw [oneBoxChildrenOdd_twoRowOneOneDiagramOdd m hm]
  have hne :
      twoRowOneOneDiagramEven m hm ≠ standardDiagramEven m (by omega) := by
    intro h
    have hrow := congrArg (fun yd => youngRow yd 2) h
    have htwo : youngRow (twoRowOneOneDiagramEven m hm) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m hm).2.2
    have hstd : youngRow (standardDiagramEven m (by omega)) 2 = 0 := by
      unfold standardDiagramEven
      rw [youngRow_twoRowDiagram]
      simp
    omega
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [tableauDim_standardDiagramEven_formula]
    rw [tableauDim_twoRowOneOneDiagramEven_formula]
    ring
  · intro hmem
    rw [Finset.mem_singleton] at hmem
    exact hne hmem.symm

theorem hOddTableau_ge_one_sixth_tableauDim_twoRowTwoOddException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowTwoException m lam) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  rw [eq_twoRowTwoDiagramOdd_of_isOddTwoRowTwoException m hm lam hshape]
  rw [hOddTableau_twoRowTwoDiagramOdd_formula m hm]
  rw [tableauDim_twoRowTwoDiagramOdd_formula m hm]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem hOddTableau_ge_one_sixth_tableauDim_twoRowOneOneOddException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hshape : IsOddTwoRowOneOneException m lam) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  rw [eq_twoRowOneOneDiagramOdd_of_isOddTwoRowOneOneException m hm lam hshape]
  rw [hOddTableau_twoRowOneOneDiagramOdd_formula m hm]
  rw [tableauDim_twoRowOneOneDiagramOdd_formula m hm]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem hOddTableau_ge_one_sixth_tableauDim_odd_exceptional
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m + 1))
    (hex : IsOddHExceptional m lam) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  rcases hex with h22 | h211
  · exact hOddTableau_ge_one_sixth_tableauDim_twoRowTwoOddException m hm lam h22
  · exact hOddTableau_ge_one_sixth_tableauDim_twoRowOneOneOddException m hm lam h211

/-- Generic odd step for tableau counts, away from one-row and standard
one-box children. -/
theorem hOddTableau_ge_one_sixth_tableauDim_of_no_bad_oneBoxChild
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hchild_row : ∀ mu ∈ oneBoxChildrenOdd m lam, ¬ IsOneRow mu)
    (hchild_std : ∀ mu ∈ oneBoxChildrenOdd m lam, ¬ IsStandard mu) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  rw [tableauDim_oneBoxChildrenOdd_branching m lam, hOddTableau]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mu hmu
  have heven :=
    S05_Lem5_32_tableau_even_certificate
      m hm mu (hchild_row mu hmu) (hchild_std mu hmu)
  have hcoeff :
      (1 / 6 : ℝ) * tableauDim mu ≤ (1 / 5 : ℝ) * tableauDim mu := by
    have hdim := tableauDim_nonneg mu
    nlinarith
  exact le_trans hcoeff heven

/-- Finite Young-diagram induction behind Lemma 5.36, using actual tableau
counts. -/
theorem hOddTableau_ge_one_sixth_tableauDim_of_not_oneRow_not_standard_finite_induction
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  by_cases hbad :
      HasOneRowOneBoxChild m lam ∨ HasStandardOneBoxChild m lam
  · exact hOddTableau_ge_one_sixth_tableauDim_odd_exceptional
      m hm lam
      (odd_bad_oneBoxChild_classification m hm lam hrow hstd hbad)
  · apply hOddTableau_ge_one_sixth_tableauDim_of_no_bad_oneBoxChild m hm lam
    · intro mu hmu hone
      exact hbad (Or.inl ⟨mu, hmu, hone⟩)
    · intro mu hmu hstandard
      exact hbad (Or.inr ⟨mu, hmu, hstandard⟩)

/-- Lemma 5.36, tableau-count version of the odd certificate. -/
theorem S05_Lem5_34_tableau_odd_certificate
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * tableauDim lam ≤ hOddTableau m lam := by
  exact
    hOddTableau_ge_one_sixth_tableauDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

/-- Generic odd step, away from one-row and standard one-box children. -/
theorem hOdd_ge_one_sixth_youngDim_of_no_bad_oneBoxChild
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hchild_row : ∀ mu ∈ oneBoxChildrenOdd m lam, ¬ IsOneRow mu)
    (hchild_std : ∀ mu ∈ oneBoxChildrenOdd m lam, ¬ IsStandard mu) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  rw [youngDim_oneBox_branching_input m lam, hOdd]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mu hmu
  have heven :=
    hEven_ge_one_fifth_youngDim_of_not_oneRow_not_standard_finite_induction
      m hm mu (hchild_row mu hmu) (hchild_std mu hmu)
  have hcoeff :
      (1 / 6 : ℝ) * youngDim mu ≤ (1 / 5 : ℝ) * youngDim mu := by
    have hdim := youngDim_nonneg mu
    nlinarith
  exact le_trans hcoeff heven

/-- Finite Young-diagram induction behind Lemma 5.36. -/
theorem hOdd_ge_one_sixth_youngDim_of_not_oneRow_not_standard_finite_induction
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  by_cases hbad :
      HasOneRowOneBoxChild m lam ∨ HasStandardOneBoxChild m lam
  · exact hOdd_ge_one_sixth_youngDim_odd_exceptional
      m hm lam
      (odd_bad_oneBoxChild_classification m hm lam hrow hstd hbad)
  · apply hOdd_ge_one_sixth_youngDim_of_no_bad_oneBoxChild m hm lam
    · intro mu hmu hone
      exact hbad (Or.inl ⟨mu, hmu, hone⟩)
    · intro mu hmu hstandard
      exact hbad (Or.inr ⟨mu, hmu, hstandard⟩)

/-- The high-weight odd count is nonnegative. -/
theorem hOdd_nonneg [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) :
    0 ≤ hOdd m lam := by
  rw [hOdd]
  exact Finset.sum_nonneg (fun mu _hmu => hEven_nonneg m mu)

/-- The high-weight odd count is bounded by the full Young dimension. -/
theorem hOdd_le_youngDim
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m + 1)) :
    hOdd m lam ≤ youngDim lam := by
  rw [hOdd, youngDim_oneBox_branching_input m lam]
  exact Finset.sum_le_sum (fun mu _hmu => hEven_le_youngDim m mu)

/-- Lemma 5.36, `lem:h-odd-app`: odd certificate.  This preserves the old
theorem name `L5_6_HOddApp`. -/
theorem L5_6_HOddApp
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  exact
    hOdd_ge_one_sixth_youngDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

/-- Lemma 5.36 paper-numbered alias: odd certificate. -/
theorem S05_Lem5_34_odd_certificate
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 6 : ℝ) * youngDim lam ≤ hOdd m lam := by
  exact L5_6_HOddApp m hm lam hrow hstd

end DictatorshipTesting
