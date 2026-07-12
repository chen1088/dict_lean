import DictatorshipTesting.Paper.Defs.S05_IntDef_HEven
import DictatorshipTesting.Paper.Defs.S05_IntDef_TableauEvenHeight
import DictatorshipTesting.Paper.Defs.S05_IntDef_CertificateSpecialDiagrams
import DictatorshipTesting.Paper.Defs.S05_IntDef_CertificateExceptionalPredicates
import DictatorshipTesting.Paper.S05_Lem5_24_WeightZeroEntriesAreNeverAMajority

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Int_EvenSpectralBridge`
- `DictatorshipTesting.Paper.S05_Int_WhereTheInductionCanFail`
- `DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate`
-/


/-!
Paper statement: Lemma 5.25 (`lem:h-even-app`)
Title in paper: Even certificate.

Status: proven. The tableau-count even certificate is proved below.  The older
`youngDim` wrapper in this file remains part of the external Specht-dimension
route.
-/

/-!
# Finite induction proof for Lemma 5.25

The intended proof uses the weight-zero bound from Lemma 5.24, the `hEven` recurrence, the dimension
recursion, and the exceptional level-two Young diagrams from Section 5.

This is deliberately not bundled into the representation-theoretic bridge:
after the dimension-recursion inputs, the paper's remaining work is finite
Young-diagram arithmetic.
-/

namespace DictatorshipTesting

/-- A positive row below the first row rules out the one-row shape. -/
theorem not_isOneRow_of_youngRow_pos {n : ℕ} (lam : YoungDiagram n)
    {i : ℕ} (hi : 1 ≤ i) (hpos : 0 < youngRow lam i) :
    ¬ IsOneRow lam := by
  intro hone
  have hzero := youngRow_eq_zero_of_isOneRow lam hone hi
  omega

/-- Row formula for the canonical three-row diagram. -/
theorem youngRow_threeRowDiagram (n a b c : ℕ) (hn : 3 ≤ n)
    (habc : a + b + c = n) (hgeab : b ≤ a) (hgebc : c ≤ b)
    (i : ℕ) :
    youngRow (threeRowDiagram n a b c hn habc hgeab hgebc) i =
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 0 := by
  unfold youngRow threeRowDiagram
  by_cases hi : i < n
  · by_cases h0 : i = 0
    · have hn0 : n ≠ 0 := by omega
      simp [h0, hn0]
    · by_cases h1 : i = 1
      · have hnle : ¬ n ≤ 1 := by omega
        simp [h1, hnle]
      · by_cases h2 : i = 2
        · have hnle : ¬ n ≤ 2 := by omega
          simp [h2, hnle]
        · simp [h0, h1, h2]
  · by_cases h0 : i = 0
    · omega
    · by_cases h1 : i = 1
      · omega
      · by_cases h2 : i = 2
        · omega
        · simp [hi, h0, h1, h2]

/-- The canonical three-row diagram is independent of proof arguments. -/
theorem threeRowDiagram_proof_irrel (n a b c : ℕ)
    (hn₁ hn₂ : 3 ≤ n) (habc₁ habc₂ : a + b + c = n)
    (hgeab₁ hgeab₂ : b ≤ a) (hgebc₁ hgebc₂ : c ≤ b) :
    threeRowDiagram n a b c hn₁ habc₁ hgeab₁ hgebc₁ =
      threeRowDiagram n a b c hn₂ habc₂ hgeab₂ hgebc₂ := by
  apply youngDiagram_ext
  intro i
  simp [youngRow_threeRowDiagram]

/-- The canonical `(2m-2,1,1)` diagram is independent of proof arguments. -/
theorem twoRowOneOneDiagramEven_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 2 ≤ m) :
    twoRowOneOneDiagramEven m hm₁ = twoRowOneOneDiagramEven m hm₂ := by
  unfold twoRowOneOneDiagramEven
  exact threeRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _ _ _ _

/-- The canonical `(2m-3,3)` diagram is independent of proof arguments. -/
theorem twoRowThreeDiagramEven_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 3 ≤ m) :
    twoRowThreeDiagramEven m hm₁ = twoRowThreeDiagramEven m hm₂ := by
  unfold twoRowThreeDiagramEven
  exact twoRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _

/-- The canonical `(2m-3,2,1)` diagram is independent of proof arguments. -/
theorem threeRowTwoOneDiagramEven_proof_irrel (m : ℕ)
    (hm₁ hm₂ : 3 ≤ m) :
    threeRowTwoOneDiagramEven m hm₁ = threeRowTwoOneDiagramEven m hm₂ := by
  unfold threeRowTwoOneDiagramEven
  exact threeRowDiagram_proof_irrel _ _ _ _ _ _ _ _ _ _ _ _

/-- The canonical `(2m-2,1,1)` satisfies its row predicate. -/
theorem isTwoRowOneOneException_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsTwoRowOneOneException m (twoRowOneOneDiagramEven m hm) := by
  unfold twoRowOneOneDiagramEven IsTwoRowOneOneException
  constructor
  · simp [youngRow_threeRowDiagram]
  constructor
  · simp [youngRow_threeRowDiagram]
  · simp [youngRow_threeRowDiagram]

/-- The canonical `(2m-3,3)` satisfies its row predicate. -/
theorem isTwoRowThreeException_twoRowThreeDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsTwoRowThreeException m (twoRowThreeDiagramEven m hm) := by
  unfold twoRowThreeDiagramEven IsTwoRowThreeException
  constructor
  · simp [youngRow_twoRowDiagram]
  · simp [youngRow_twoRowDiagram]

/-- The canonical `(2m-3,2,1)` satisfies its row predicate. -/
theorem isThreeRowTwoOneException_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsThreeRowTwoOneException m (threeRowTwoOneDiagramEven m hm) := by
  unfold threeRowTwoOneDiagramEven IsThreeRowTwoOneException
  constructor
  · simp [youngRow_threeRowDiagram]
  constructor
  · simp [youngRow_threeRowDiagram]
  · simp [youngRow_threeRowDiagram]

/-- The standard diagram is not one-row. -/
theorem not_isOneRow_standardDiagramEven (m : ℕ) (hm : 1 ≤ m) :
    ¬ IsOneRow (standardDiagramEven m hm) := by
  apply not_isOneRow_of_youngRow_pos (standardDiagramEven m hm) (i := 1) (by omega)
  have h1 := (isStandard_standardDiagramEven m hm).2.2
  omega

/-- The `(2m-2,2)` diagram is not one-row. -/
theorem not_isOneRow_twoRowTwoDiagramEven (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsOneRow (twoRowTwoDiagramEven m hm) := by
  apply not_isOneRow_of_youngRow_pos (twoRowTwoDiagramEven m hm) (i := 1) (by omega)
  have h1 := (isTwoRowTwoException_twoRowTwoDiagramEven m hm).2
  omega

/-- The `(2m-2,1,1)` diagram is not one-row. -/
theorem not_isOneRow_twoRowOneOneDiagramEven (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsOneRow (twoRowOneOneDiagramEven m hm) := by
  apply not_isOneRow_of_youngRow_pos (twoRowOneOneDiagramEven m hm) (i := 1) (by omega)
  have h1 := (isTwoRowOneOneException_twoRowOneOneDiagramEven m hm).2.1
  omega

/-- If the second represented row is zero, then every later row is zero. -/
theorem youngRow_eq_zero_of_one_le_of_youngRow_one_eq_zero {n : ℕ}
    (hn : 1 < n) (lam : YoungDiagram n) (h1 : youngRow lam 1 = 0)
    {i : ℕ} (hi : 1 ≤ i) :
    youngRow lam i = 0 := by
  unfold youngRow
  by_cases hin : i < n
  · have h1row : (lam.row (Fin.mk 1 hn) : ℕ) = 0 := by
      unfold youngRow at h1
      simp [hn] at h1
      exact_mod_cast h1
    have hle := lam.nonincreasing
      (i := Fin.mk 1 hn) (j := Fin.mk i hin) hi
    have hrow_le_zero : (lam.row (Fin.mk i hin) : ℕ) ≤ 0 := by
      simpa [h1row] using hle
    have hrow_zero : (lam.row (Fin.mk i hin) : ℕ) = 0 := by
      omega
    simp [hin, hrow_zero]
  · simp [hin]

/-- If every row from the fourth row onward is zero, then the first three rows
exhaust the size of the diagram. -/
theorem youngRow_zero_add_one_add_two_eq_size_of_tail_zero {n : ℕ}
    (hn : 3 ≤ n) (lam : YoungDiagram n)
    (htail : ∀ {i : ℕ}, 3 ≤ i → youngRow lam i = 0) :
    youngRow lam 0 + youngRow lam 1 + youngRow lam 2 = n := by
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
  have htail2_zero :
      tail2.sum (fun x => (lam.row x : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx_erase2 := Finset.mem_erase.mp hx
    have hxne2 : Not (x = i2) := hx_erase2.1
    have hx_tail1 := hx_erase2.2
    have hx_erase1 := Finset.mem_erase.mp hx_tail1
    have hxne1 : Not (x = i1) := hx_erase1.1
    have hx_tail0 := hx_erase1.2
    have hx_erase0 := Finset.mem_erase.mp hx_tail0
    have hxne0 : Not (x = i0) := hx_erase0.1
    have hxge3 : 3 ≤ (x : ℕ) := by
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
      have hxne2val : (x : ℕ) ≠ 2 := by
        intro h
        apply hxne2
        ext
        simp [i2, h]
      omega
    have hzero := htail hxge3
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
  have hsum2 :
      (lam.row i2 : ℕ) + tail2.sum (fun x => (lam.row x : ℕ)) =
        tail1.sum (fun x => (lam.row x : ℕ)) := by
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
  omega

/-- If the first three rows already contain all boxes, then all later rows are
zero. -/
theorem youngRow_eq_zero_of_three_le_of_first_three_sum {n : ℕ}
    (hn : 3 ≤ n) (lam : YoungDiagram n)
    (hsum012 : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 = n)
    {i : ℕ} (hi : 3 ≤ i) :
    youngRow lam i = 0 := by
  classical
  by_cases hin : i < n
  · have h0n : 0 < n := by omega
    have h1n : 1 < n := by omega
    have h2n : 2 < n := by omega
    let i0 : Fin n := Fin.mk 0 h0n
    let i1 : Fin n := Fin.mk 1 h1n
    let i2 : Fin n := Fin.mk 2 h2n
    let ii : Fin n := Fin.mk i hin
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
    have hne_i2 : Not (ii = i2) := by
      intro h
      have hv : (ii : ℕ) = (i2 : ℕ) := by
        simpa using congrArg Fin.val h
      simp [ii, i2] at hv
      omega
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
    have hii_tail2 : ii ∈ tail2 := by
      dsimp [tail2, tail1, tail0]
      exact Finset.mem_erase.mpr
        ⟨hne_i2,
          Finset.mem_erase.mpr
            ⟨hne_i1, Finset.mem_erase.mpr ⟨hne_i0, Finset.mem_univ ii⟩⟩⟩
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
          tail1.sum (fun x => (lam.row x : ℕ)) := by
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
    have htail_zero : tail2.sum (fun x => (lam.row x : ℕ)) = 0 := by
      omega
    have hii_le_tail :
        (lam.row ii : ℕ) ≤ tail2.sum (fun x => (lam.row x : ℕ)) := by
      exact
        Finset.single_le_sum
          (s := tail2) (f := fun x : Fin n => (lam.row x : ℕ))
          (fun x _hx => Nat.zero_le (lam.row x : ℕ))
          hii_tail2
    have hii_zero : (lam.row ii : ℕ) = 0 := by
      omega
    unfold youngRow
    simp [ii, hin, hii_zero]
  · unfold youngRow
    simp [hin]

/-- A diagram whose first three rows are `(a,b,c)` and exhaust the size is the
canonical three-row diagram. -/
theorem eq_threeRowDiagram_of_rows {n a b c : ℕ} (hn : 3 ≤ n)
    (habc : a + b + c = n) (hgeab : b ≤ a) (hgebc : c ≤ b)
    (lam : YoungDiagram n)
    (h0 : youngRow lam 0 = a) (h1 : youngRow lam 1 = b)
    (h2 : youngRow lam 2 = c) :
    lam = threeRowDiagram n a b c hn habc hgeab hgebc := by
  apply youngDiagram_ext
  intro i
  rw [youngRow_threeRowDiagram]
  by_cases hi0 : i = 0
  · subst i
    exact h0
  · by_cases hi1 : i = 1
    · subst i
      simp [h1]
    · by_cases hi2 : i = 2
      · subst i
        simp [h2]
      · have hsum012 : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 = n := by
          omega
        have hige3 : 3 ≤ i := by omega
        simp [hi0, hi1, hi2,
          youngRow_eq_zero_of_three_le_of_first_three_sum hn lam hsum012 hige3]

/-- A `(2m-2,1,1)` row predicate identifies the canonical diagram. -/
theorem eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowOneOneException m lam) :
    lam = twoRowOneOneDiagramEven m hm := by
  rcases hshape with ⟨h0, h1, h2⟩
  unfold twoRowOneOneDiagramEven
  exact
    eq_threeRowDiagram_of_rows
      (n := 2 * m) (a := 2 * m - 2) (b := 1) (c := 1)
      (by omega) (by omega) (by omega) (by omega) lam h0 h1 h2

/-- A `(2m-3,3)` row predicate identifies the canonical diagram. -/
theorem eq_twoRowThreeDiagramEven_of_isTwoRowThreeException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowThreeException m lam) :
    lam = twoRowThreeDiagramEven m hm := by
  rcases hshape with ⟨h0, h1⟩
  unfold twoRowThreeDiagramEven
  exact
    eq_twoRowDiagram_of_rows
      (n := 2 * m) (a := 2 * m - 3) (b := 3)
      (by omega) (by omega) (by omega) lam h0 h1

/-- A `(2m-3,2,1)` row predicate identifies the canonical diagram. -/
theorem eq_threeRowTwoOneDiagramEven_of_isThreeRowTwoOneException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsThreeRowTwoOneException m lam) :
    lam = threeRowTwoOneDiagramEven m hm := by
  rcases hshape with ⟨h0, h1, h2⟩
  unfold threeRowTwoOneDiagramEven
  exact
    eq_threeRowDiagram_of_rows
      (n := 2 * m) (a := 2 * m - 3) (b := 2) (c := 1)
      (by omega) (by omega) (by omega) (by omega) lam h0 h1 h2

/-- The standard child of `(2m-2,1,1)` obtained by deleting the first row's
two extra boxes. -/
theorem standardDiagramEven_horizontalChild_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsHorizontalTwoStripChild (twoRowOneOneDiagramEven m hm)
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowOneOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold twoRowOneOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1]

/-- The smaller `(2m-4,1,1)` child of `(2m-2,1,1)`. -/
theorem twoRowOneOneDiagramEven_horizontalChild_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (twoRowOneOneDiagramEven m (by omega))
      (twoRowOneOneDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · have hi10 : (i : ℕ) + 1 ≠ 0 := by omega
          have hi11 : (i : ℕ) + 1 ≠ 1 := by omega
          have hi12 : (i : ℕ) + 1 ≠ 2 := by omega
          simp [hi0, hi1, hi2, hi12]

/-- The one-row vertical child of `(2m-2,1,1)`. -/
theorem oneRowDiagram_verticalChild_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsVerticalTwoStripChild (twoRowOneOneDiagramEven m hm)
      (oneRowDiagram (2 * (m - 1))) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_oneRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_oneRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- The standard vertical child of `(2m-2,1,1)`. -/
theorem standardDiagramEven_verticalChild_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 2 ≤ m) :
    IsVerticalTwoStripChild (twoRowOneOneDiagramEven m hm)
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowOneOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold twoRowOneOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- Horizontal children of `(2m-2,1,1)` are standard or the smaller
`(2m-4,1,1)` shape. -/
theorem horizontalChild_twoRowOneOneDiagramEven_classification
    (m : ℕ) (hm : 3 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsHorizontalTwoStripChild (twoRowOneOneDiagramEven m (by omega)) mu) :
    mu = standardDiagramEven (m - 1) (by omega) ∨
      mu = twoRowOneOneDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) i = 0 := by
        unfold twoRowOneOneDiagramEven
        rw [youngRow_threeRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        have hi2 : i ≠ 2 := by omega
        simp [hi0, hi1, hi2]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum012 :
      youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_add_two_eq_size_of_tail_zero
      (by omega : 3 ≤ 2 * (m - 1)) mu htail
  have hmu1_le : youngRow mu 1 ≤ 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 1 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).2.1
    simpa [i1, hparent] using hsub
  have hmu1_ge : 1 ≤ youngRow mu 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hle := hstrip.2.2 i1
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).2.2
    simpa [i1, hparent] using hle
  have hmu1 : youngRow mu 1 = 1 := by omega
  have hmu2_le : youngRow mu 2 ≤ 1 := by
    let i2 : Fin (2 * m) := Fin.mk 2 (by omega)
    have hsub := hstrip.2.1 i2
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).2.2
    simpa [i2, hparent] using hsub
  have hmu2_cases : youngRow mu 2 = 0 ∨ youngRow mu 2 = 1 := by omega
  rcases hmu2_cases with hmu2 | hmu2
  · left
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1
  · right
    apply eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException (m - 1) (by omega)
    unfold IsTwoRowOneOneException
    constructor
    · omega
    constructor
    · exact hmu1
    · exact hmu2

/-- The horizontal child set of `(2,1,1)` consists only of `(1,1)`. -/
theorem horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven_two :
    horizontalTwoStripChildrenEven 2 (twoRowOneOneDiagramEven 2 (by omega)) =
      {standardDiagramEven 1 (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowOneOneDiagramEven 2 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    have hmu1_le : youngRow mu 1 ≤ 1 := by
      let i1 : Fin (2 * 2) := Fin.mk 1 (by omega)
      have hsub := hstrip.2.1 i1
      have hparent : youngRow (twoRowOneOneDiagramEven 2 (by omega)) 1 = 1 :=
        (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.1
      simpa [i1, hparent] using hsub
    have hmu1_ge : 1 ≤ youngRow mu 1 := by
      let i1 : Fin (2 * 2) := Fin.mk 1 (by omega)
      have hle := hstrip.2.2 i1
      have hparent : youngRow (twoRowOneOneDiagramEven 2 (by omega)) 2 = 1 :=
        (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.2
      simpa [i1, hparent] using hle
    have hmu1 : youngRow mu 1 = 1 := by omega
    have hsum01 : youngRow mu 0 + youngRow mu 1 = 2 := by
      exact youngRow_zero_add_one_eq_size_of_tail_zero
        (by omega : 2 ≤ 2) mu (by
          intro i hi
          unfold youngRow
          simp [show ¬ i < 2 by omega])
    have hstd : IsStandard mu := by
      unfold IsStandard
      constructor
      · omega
      constructor
      · omega
      · exact hmu1
    exact Finset.mem_singleton.mpr
      (eq_standardDiagramEven_of_isStandard 1 (by omega) mu hstd)
  · intro hmu
    have hmu_eq : mu = standardDiagramEven 1 (by omega) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold horizontalTwoStripChildrenEven
    simp [standardDiagramEven_horizontalChild_twoRowOneOneDiagramEven 2 (by omega)]

/-- Horizontal children of `(2m-2,1,1)` for `m ≥ 3`, as a concrete Finset. -/
theorem horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    horizontalTwoStripChildrenEven m (twoRowOneOneDiagramEven m (by omega)) =
      {standardDiagramEven (m - 1) (by omega),
        twoRowOneOneDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowOneOneDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases horizontalChild_twoRowOneOneDiagramEven_classification m hm mu hstrip with
      hstd | h211
    · exact Finset.mem_insert.mpr (Or.inl hstd)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr h211))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hstd | h211
    · subst hstd
      simp [standardDiagramEven_horizontalChild_twoRowOneOneDiagramEven m (by omega)]
    · subst h211
      simp [twoRowOneOneDiagramEven_horizontalChild_twoRowOneOneDiagramEven m hm]

/-- The vertical child set of `(2,1,1)` consists of `(2)` and `(1,1)`. -/
theorem verticalTwoStripChildrenEven_twoRowOneOneDiagramEven_two :
    verticalTwoStripChildrenEven 2 (twoRowOneOneDiagramEven 2 (by omega)) =
      {oneRowDiagram 2, standardDiagramEven 1 (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (twoRowOneOneDiagramEven 2 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    have hsum01 : youngRow mu 0 + youngRow mu 1 = 2 := by
      exact youngRow_zero_add_one_eq_size_of_tail_zero
        (by omega : 2 ≤ 2) mu (by
          intro i hi
          unfold youngRow
          simp [show ¬ i < 2 by omega])
    have hmu0_ge : 1 ≤ youngRow mu 0 := by
      let i0 : Fin (2 * 2) := Fin.mk 0 (by omega)
      have hle := hstrip.2.2 i0
      have hparent : youngRow (twoRowOneOneDiagramEven 2 (by omega)) 0 = 2 :=
        (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).1
      have hle' : 2 ≤ youngRow mu 0 + 1 := by
        simpa [i0, hparent] using hle
      omega
    have hmu0_le : youngRow mu 0 ≤ 2 := youngRow_le_size mu 0
    have hmu0_cases : youngRow mu 0 = 2 ∨ youngRow mu 0 = 1 := by omega
    rcases hmu0_cases with hmu0 | hmu0
    · exact Finset.mem_insert.mpr (Or.inl
        (eq_oneRowDiagram_of_isOneRow mu (by
          unfold IsOneRow
          exact hmu0)))
    · have hmu1 : youngRow mu 1 = 1 := by omega
      have hstd : IsStandard mu := by
        unfold IsStandard
        constructor
        · omega
        constructor
        · omega
        · exact hmu1
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr
          (eq_standardDiagramEven_of_isStandard 1 (by omega) mu hstd)))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold verticalTwoStripChildrenEven
    rcases hmu with hone | hstd
    · subst hone
      simp [oneRowDiagram_verticalChild_twoRowOneOneDiagramEven 2 (by omega)]
    · subst hstd
      simp [standardDiagramEven_verticalChild_twoRowOneOneDiagramEven 2 (by omega)]

/-- Vertical children of `(2m-2,1,1)` are one-row or standard. -/
theorem verticalChild_twoRowOneOneDiagramEven_classification
    (m : ℕ) (hm : 3 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsVerticalTwoStripChild (twoRowOneOneDiagramEven m (by omega)) mu) :
    mu = oneRowDiagram (2 * (m - 1)) ∨
      mu = standardDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) i = 0 := by
        unfold twoRowOneOneDiagramEven
        rw [youngRow_threeRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        have hi2 : i ≠ 2 := by omega
        simp [hi0, hi1, hi2]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum012 :
      youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_add_two_eq_size_of_tail_zero
      (by omega : 3 ≤ 2 * (m - 1)) mu htail
  have hmu0_ge : 2 * m - 3 ≤ youngRow mu 0 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 0 = 2 * m - 2 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).1
    have hle' : 2 * m - 2 ≤ youngRow mu 0 + 1 := by
      simpa [i0, hparent] using hle
    omega
  have hmu0_le : youngRow mu 0 ≤ 2 * m - 2 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hsub := hstrip.2.1 i0
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 0 = 2 * m - 2 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).1
    simpa [i0, hparent] using hsub
  have hmu1_le : youngRow mu 1 ≤ 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 1 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).2.1
    simpa [i1, hparent] using hsub
  have hmu2_le : youngRow mu 2 ≤ 1 := by
    let i2 : Fin (2 * m) := Fin.mk 2 (by omega)
    have hsub := hstrip.2.1 i2
    have hparent : youngRow (twoRowOneOneDiagramEven m (by omega)) 2 = 1 :=
      (isTwoRowOneOneException_twoRowOneOneDiagramEven m (by omega)).2.2
    simpa [i2, hparent] using hsub
  have hmu0_cases :
      youngRow mu 0 = 2 * m - 2 ∨ youngRow mu 0 = 2 * m - 3 := by
    omega
  rcases hmu0_cases with hmu0 | hmu0
  · left
    apply eq_oneRowDiagram_of_isOneRow
    unfold IsOneRow
    omega
  · right
    have hmu2_le_mu1 : youngRow mu 2 ≤ youngRow mu 1 := by
      unfold youngRow
      have h1 : 1 < 2 * (m - 1) := by omega
      have h2 : 2 < 2 * (m - 1) := by omega
      have hle := mu.nonincreasing
        (i := Fin.mk 1 h1) (j := Fin.mk 2 h2) (by norm_num)
      simpa [h1, h2] using hle
    have hmu1 : youngRow mu 1 = 1 := by omega
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1

/-- Vertical children of `(2m-2,1,1)`, as a concrete Finset. -/
theorem verticalTwoStripChildrenEven_twoRowOneOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    verticalTwoStripChildrenEven m (twoRowOneOneDiagramEven m (by omega)) =
      {oneRowDiagram (2 * (m - 1)), standardDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (twoRowOneOneDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases verticalChild_twoRowOneOneDiagramEven_classification m hm mu hstrip with
      hone | hstd
    · exact Finset.mem_insert.mpr (Or.inl hone)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr hstd))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold verticalTwoStripChildrenEven
    rcases hmu with hone | hstd
    · subst hone
      simp [oneRowDiagram_verticalChild_twoRowOneOneDiagramEven m (by omega)]
    · subst hstd
      simp [standardDiagramEven_verticalChild_twoRowOneOneDiagramEven m (by omega)]

/-- The standard horizontal child of `(2m-3,3)`. -/
theorem standardDiagramEven_horizontalChild_twoRowThreeDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (twoRowThreeDiagramEven m hm)
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowThreeDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowThreeDiagramEven standardDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The `(2m-4,2)` horizontal child of `(2m-3,3)`. -/
theorem twoRowTwoDiagramEven_horizontalChild_twoRowThreeDiagramEven
    (m : ℕ) (hm : 4 ≤ m) :
    IsHorizontalTwoStripChild (twoRowThreeDiagramEven m (by omega))
      (twoRowTwoDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowThreeDiagramEven twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowThreeDiagramEven twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The smaller `(2m-5,3)` horizontal child of `(2m-3,3)`. -/
theorem twoRowThreeDiagramEven_horizontalChild_twoRowThreeDiagramEven
    (m : ℕ) (hm : 4 ≤ m) :
    IsHorizontalTwoStripChild (twoRowThreeDiagramEven m (by omega))
      (twoRowThreeDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowThreeDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowThreeDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- The `(2m-4,2)` vertical child of `(2m-3,3)`. -/
theorem twoRowTwoDiagramEven_verticalChild_twoRowThreeDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsVerticalTwoStripChild (twoRowThreeDiagramEven m hm)
      (twoRowTwoDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold twoRowThreeDiagramEven twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]
  · intro i
    unfold twoRowThreeDiagramEven twoRowTwoDiagramEven
    rw [youngRow_twoRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · simp [hi0, hi1]

/-- Horizontal children of `(2m-3,3)` are standard, `(2m-4,2)`,
or the smaller `(2m-5,3)`. -/
theorem horizontalChild_twoRowThreeDiagramEven_classification
    (m : ℕ) (hm : 4 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsHorizontalTwoStripChild (twoRowThreeDiagramEven m (by omega)) mu) :
    mu = standardDiagramEven (m - 1) (by omega) ∨
      mu = twoRowTwoDiagramEven (m - 1) (by omega) ∨
        mu = twoRowThreeDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (twoRowThreeDiagramEven m (by omega)) i = 0 := by
        unfold twoRowThreeDiagramEven
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
  have hmu0_ge : 3 ≤ youngRow mu 0 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (twoRowThreeDiagramEven m (by omega)) 1 = 3 :=
      (isTwoRowThreeException_twoRowThreeDiagramEven m (by omega)).2
    simpa [i0, hparent] using hle
  have hmu0_le : youngRow mu 0 ≤ 2 * m - 3 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hsub := hstrip.2.1 i0
    have hparent : youngRow (twoRowThreeDiagramEven m (by omega)) 0 = 2 * m - 3 :=
      (isTwoRowThreeException_twoRowThreeDiagramEven m (by omega)).1
    simpa [i0, hparent] using hsub
  have hmu1_le : youngRow mu 1 ≤ 3 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (twoRowThreeDiagramEven m (by omega)) 1 = 3 :=
      (isTwoRowThreeException_twoRowThreeDiagramEven m (by omega)).2
    simpa [i1, hparent] using hsub
  have hmu1_cases :
      youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 ∨ youngRow mu 1 = 3 := by
    omega
  rcases hmu1_cases with hmu1 | hrest
  · left
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1
  rcases hrest with hmu1 | hmu1
  · right
    left
    apply eq_twoRowTwoDiagramEven_of_isTwoRowTwoException (m - 1) (by omega)
    unfold IsTwoRowTwoException
    constructor
    · omega
    · exact hmu1
  · right
    right
    apply eq_twoRowThreeDiagramEven_of_isTwoRowThreeException (m - 1) (by omega)
    unfold IsTwoRowThreeException
    constructor
    · omega
    · exact hmu1

/-- Horizontal children of `(3,3)`. -/
theorem horizontalTwoStripChildrenEven_twoRowThreeDiagramEven_three :
    horizontalTwoStripChildrenEven 3 (twoRowThreeDiagramEven 3 (by omega)) =
      {standardDiagramEven 2 (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowThreeDiagramEven 3 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * (3 - 1)
      · let ib : Fin (2 * 3) := Fin.mk i (by omega)
        have hsub := hstrip.2.1 ib
        have hparent : youngRow (twoRowThreeDiagramEven 3 (by omega)) i = 0 := by
          unfold twoRowThreeDiagramEven
          rw [youngRow_twoRowDiagram]
          have hi0 : i ≠ 0 := by omega
          have hi1 : i ≠ 1 := by omega
          simp [hi0, hi1]
        have hle0 : youngRow mu i ≤ 0 := by
          simpa [ib, hparent] using hsub
        omega
      · unfold youngRow
        simp [hin]
    have hsum01 : youngRow mu 0 + youngRow mu 1 = 4 := by
      exact youngRow_zero_add_one_eq_size_of_tail_zero
        (by omega : 2 ≤ 4) mu htail
    have hmu0_ge : 3 ≤ youngRow mu 0 := by
      let i0 : Fin (2 * 3) := Fin.mk 0 (by omega)
      have hle := hstrip.2.2 i0
      have hparent : youngRow (twoRowThreeDiagramEven 3 (by omega)) 1 = 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven 3 (by omega)).2
      simpa [i0, hparent] using hle
    have hmu0_le : youngRow mu 0 ≤ 3 := by
      let i0 : Fin (2 * 3) := Fin.mk 0 (by omega)
      have hsub := hstrip.2.1 i0
      have hparent : youngRow (twoRowThreeDiagramEven 3 (by omega)) 0 = 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven 3 (by omega)).1
      simpa [i0, hparent] using hsub
    have hmu1 : youngRow mu 1 = 1 := by omega
    have hstd : IsStandard mu := by
      unfold IsStandard
      constructor
      · omega
      constructor
      · omega
      · exact hmu1
    exact Finset.mem_singleton.mpr
      (eq_standardDiagramEven_of_isStandard 2 (by omega) mu hstd)
  · intro hmu
    have hmu_eq : mu = standardDiagramEven 2 (by omega) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold horizontalTwoStripChildrenEven
    simp [standardDiagramEven_horizontalChild_twoRowThreeDiagramEven 3 (by omega)]

/-- Horizontal children of `(2m-3,3)` for `m ≥ 4`, as a concrete Finset. -/
theorem horizontalTwoStripChildrenEven_twoRowThreeDiagramEven
    (m : ℕ) (hm : 4 ≤ m) :
    horizontalTwoStripChildrenEven m (twoRowThreeDiagramEven m (by omega)) =
      {standardDiagramEven (m - 1) (by omega),
        twoRowTwoDiagramEven (m - 1) (by omega),
        twoRowThreeDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (twoRowThreeDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases horizontalChild_twoRowThreeDiagramEven_classification m hm mu hstrip with
      hstd | hrest
    · exact Finset.mem_insert.mpr (Or.inl hstd)
    rcases hrest with h22 | h33
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl h22)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr h33))))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hstd | hrest
    · subst hstd
      simp [standardDiagramEven_horizontalChild_twoRowThreeDiagramEven m (by omega)]
    rcases hrest with h22 | h33
    · subst h22
      simp [twoRowTwoDiagramEven_horizontalChild_twoRowThreeDiagramEven m hm]
    · subst h33
      simp [twoRowThreeDiagramEven_horizontalChild_twoRowThreeDiagramEven m hm]

/-- Vertical children of `(2m-3,3)`, as a concrete Finset. -/
theorem verticalTwoStripChildrenEven_twoRowThreeDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    verticalTwoStripChildrenEven m (twoRowThreeDiagramEven m hm) =
      {twoRowTwoDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (twoRowThreeDiagramEven m hm) mu :=
      (Finset.mem_filter.mp hmu).2
    have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * (m - 1)
      · let ib : Fin (2 * m) := Fin.mk i (by omega)
        have hsub := hstrip.2.1 ib
        have hparent : youngRow (twoRowThreeDiagramEven m hm) i = 0 := by
          unfold twoRowThreeDiagramEven
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
    have hmu0_ge : 2 * m - 4 ≤ youngRow mu 0 := by
      let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
      have hle := hstrip.2.2 i0
      have hparent : youngRow (twoRowThreeDiagramEven m hm) 0 = 2 * m - 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven m hm).1
      have hle' : 2 * m - 3 ≤ youngRow mu 0 + 1 := by
        simpa [i0, hparent] using hle
      omega
    have hmu0_le : youngRow mu 0 ≤ 2 * m - 3 := by
      let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
      have hsub := hstrip.2.1 i0
      have hparent : youngRow (twoRowThreeDiagramEven m hm) 0 = 2 * m - 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven m hm).1
      simpa [i0, hparent] using hsub
    have hmu1_ge : 2 ≤ youngRow mu 1 := by
      let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
      have hle := hstrip.2.2 i1
      have hparent : youngRow (twoRowThreeDiagramEven m hm) 1 = 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven m hm).2
      have hle' : 3 ≤ youngRow mu 1 + 1 := by
        simpa [i1, hparent] using hle
      omega
    have hmu1_le : youngRow mu 1 ≤ 3 := by
      let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
      have hsub := hstrip.2.1 i1
      have hparent : youngRow (twoRowThreeDiagramEven m hm) 1 = 3 :=
        (isTwoRowThreeException_twoRowThreeDiagramEven m hm).2
      simpa [i1, hparent] using hsub
    have hmu1 : youngRow mu 1 = 2 := by omega
    have hshape : IsTwoRowTwoException (m - 1) mu := by
      unfold IsTwoRowTwoException
      constructor
      · omega
      · exact hmu1
    exact Finset.mem_singleton.mpr
      (eq_twoRowTwoDiagramEven_of_isTwoRowTwoException (m - 1) (by omega) mu hshape)
  · intro hmu
    have hmu_eq : mu = twoRowTwoDiagramEven (m - 1) (by omega) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [twoRowTwoDiagramEven_verticalChild_twoRowThreeDiagramEven m hm]

/-- The standard horizontal child of `(2m-3,2,1)`. -/
theorem standardDiagramEven_horizontalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1]

/-- The `(2m-4,2)` horizontal child of `(2m-3,2,1)`. -/
theorem twoRowTwoDiagramEven_horizontalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (twoRowTwoDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowTwoDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowTwoDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1]

/-- The `(2m-4,1,1)` horizontal child of `(2m-3,2,1)`. -/
theorem twoRowOneOneDiagramEven_horizontalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (twoRowOneOneDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · have hi10 : (i : ℕ) + 1 ≠ 0 := by omega
          have hi11 : (i : ℕ) + 1 ≠ 1 := by omega
          have hi12 : (i : ℕ) + 1 ≠ 2 := by omega
          simp [hi0, hi1, hi2, hi12]

/-- The smaller `(2m-5,2,1)` horizontal child of `(2m-3,2,1)`. -/
theorem threeRowTwoOneDiagramEven_horizontalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 4 ≤ m) :
    IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m (by omega))
      (threeRowTwoOneDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · have hi10 : (i : ℕ) + 1 ≠ 0 := by omega
          have hi11 : (i : ℕ) + 1 ≠ 1 := by omega
          have hi12 : (i : ℕ) + 1 ≠ 2 := by omega
          simp [hi0, hi1, hi2, hi12]

/-- The standard vertical child of `(2m-3,2,1)`. -/
theorem standardDiagramEven_verticalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsVerticalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (standardDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven standardDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- The `(2m-4,2)` vertical child of `(2m-3,2,1)`. -/
theorem twoRowTwoDiagramEven_verticalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsVerticalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (twoRowTwoDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowTwoDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowTwoDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- The `(2m-4,1,1)` vertical child of `(2m-3,2,1)`. -/
theorem twoRowOneOneDiagramEven_verticalChild_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    IsVerticalTwoStripChild (threeRowTwoOneDiagramEven m hm)
      (twoRowOneOneDiagramEven (m - 1) (by omega)) := by
  constructor
  · omega
  constructor
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]
  · intro i
    unfold threeRowTwoOneDiagramEven twoRowOneOneDiagramEven
    rw [youngRow_threeRowDiagram, youngRow_threeRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
      omega
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · simp [hi0, hi1, hi2]

/-- Horizontal children of `(2m-3,2,1)` are standard, `(2m-4,2)`,
`(2m-4,1,1)`, or the smaller `(2m-5,2,1)`. -/
theorem horizontalChild_threeRowTwoOneDiagramEven_classification
    (m : ℕ) (hm : 4 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m (by omega)) mu) :
    mu = standardDiagramEven (m - 1) (by omega) ∨
      mu = twoRowTwoDiagramEven (m - 1) (by omega) ∨
        mu = twoRowOneOneDiagramEven (m - 1) (by omega) ∨
          mu = threeRowTwoOneDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (threeRowTwoOneDiagramEven m (by omega)) i = 0 := by
        unfold threeRowTwoOneDiagramEven
        rw [youngRow_threeRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        have hi2 : i ≠ 2 := by omega
        simp [hi0, hi1, hi2]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum012 :
      youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_add_two_eq_size_of_tail_zero
      (by omega : 3 ≤ 2 * (m - 1)) mu htail
  have hmu1_ge : 1 ≤ youngRow mu 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hle := hstrip.2.2 i1
    have hparent : youngRow (threeRowTwoOneDiagramEven m (by omega)) 2 = 1 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m (by omega)).2.2
    simpa [i1, hparent] using hle
  have hmu1_le : youngRow mu 1 ≤ 2 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (threeRowTwoOneDiagramEven m (by omega)) 1 = 2 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m (by omega)).2.1
    simpa [i1, hparent] using hsub
  have hmu2_le : youngRow mu 2 ≤ 1 := by
    let i2 : Fin (2 * m) := Fin.mk 2 (by omega)
    have hsub := hstrip.2.1 i2
    have hparent : youngRow (threeRowTwoOneDiagramEven m (by omega)) 2 = 1 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m (by omega)).2.2
    simpa [i2, hparent] using hsub
  have hmu1_cases : youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 := by omega
  have hmu2_cases : youngRow mu 2 = 0 ∨ youngRow mu 2 = 1 := by omega
  rcases hmu1_cases with hmu1 | hmu1 <;> rcases hmu2_cases with hmu2 | hmu2
  · left
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1
  · right
    right
    left
    apply eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException (m - 1) (by omega)
    unfold IsTwoRowOneOneException
    constructor
    · omega
    constructor
    · exact hmu1
    · exact hmu2
  · right
    left
    apply eq_twoRowTwoDiagramEven_of_isTwoRowTwoException (m - 1) (by omega)
    unfold IsTwoRowTwoException
    constructor
    · omega
    · exact hmu1
  · right
    right
    right
    apply eq_threeRowTwoOneDiagramEven_of_isThreeRowTwoOneException (m - 1) (by omega)
    unfold IsThreeRowTwoOneException
    constructor
    · omega
    constructor
    · exact hmu1
    · exact hmu2

/-- Horizontal children of `(3,2,1)`. -/
theorem horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven_three :
    horizontalTwoStripChildrenEven 3 (threeRowTwoOneDiagramEven 3 (by omega)) =
      {standardDiagramEven 2 (by omega),
        twoRowTwoDiagramEven 2 (by omega),
        twoRowOneOneDiagramEven 2 (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven 3 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
      intro i hi
      by_cases hin : i < 2 * (3 - 1)
      · let ib : Fin (2 * 3) := Fin.mk i (by omega)
        have hsub := hstrip.2.1 ib
        have hparent : youngRow (threeRowTwoOneDiagramEven 3 (by omega)) i = 0 := by
          unfold threeRowTwoOneDiagramEven
          rw [youngRow_threeRowDiagram]
          have hi0 : i ≠ 0 := by omega
          have hi1 : i ≠ 1 := by omega
          have hi2 : i ≠ 2 := by omega
          simp [hi0, hi1, hi2]
        have hle0 : youngRow mu i ≤ 0 := by
          simpa [ib, hparent] using hsub
        omega
      · unfold youngRow
        simp [hin]
    have hsum012 : youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 4 := by
      exact youngRow_zero_add_one_add_two_eq_size_of_tail_zero
        (by omega : 3 ≤ 4) mu htail
    have hmu1_ge : 1 ≤ youngRow mu 1 := by
      let i1 : Fin (2 * 3) := Fin.mk 1 (by omega)
      have hle := hstrip.2.2 i1
      have hparent : youngRow (threeRowTwoOneDiagramEven 3 (by omega)) 2 = 1 :=
        (isThreeRowTwoOneException_threeRowTwoOneDiagramEven 3 (by omega)).2.2
      simpa [i1, hparent] using hle
    have hmu1_le : youngRow mu 1 ≤ 2 := by
      let i1 : Fin (2 * 3) := Fin.mk 1 (by omega)
      have hsub := hstrip.2.1 i1
      have hparent : youngRow (threeRowTwoOneDiagramEven 3 (by omega)) 1 = 2 :=
        (isThreeRowTwoOneException_threeRowTwoOneDiagramEven 3 (by omega)).2.1
      simpa [i1, hparent] using hsub
    have hmu2_le : youngRow mu 2 ≤ 1 := by
      let i2 : Fin (2 * 3) := Fin.mk 2 (by omega)
      have hsub := hstrip.2.1 i2
      have hparent : youngRow (threeRowTwoOneDiagramEven 3 (by omega)) 2 = 1 :=
        (isThreeRowTwoOneException_threeRowTwoOneDiagramEven 3 (by omega)).2.2
      simpa [i2, hparent] using hsub
    have hmu1_le_mu0 : youngRow mu 1 ≤ youngRow mu 0 := by
      unfold youngRow
      have hle := mu.nonincreasing
        (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
      simpa using hle
    have hmu1_cases : youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 := by omega
    have hmu2_cases : youngRow mu 2 = 0 ∨ youngRow mu 2 = 1 := by omega
    rcases hmu1_cases with hmu1 | hmu1 <;> rcases hmu2_cases with hmu2 | hmu2
    · exact Finset.mem_insert.mpr (Or.inl
        (eq_standardDiagramEven_of_isStandard 2 (by omega) mu (by
          unfold IsStandard
          constructor
          · omega
          constructor
          · omega
          · exact hmu1)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr
            (eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException 2 (by omega) mu (by
              unfold IsTwoRowOneOneException
              constructor
              · omega
              constructor
              · exact hmu1
              · exact hmu2))))))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inl
            (eq_twoRowTwoDiagramEven_of_isTwoRowTwoException 2 (by omega) mu (by
              unfold IsTwoRowTwoException
              constructor
              · omega
              · exact hmu1)))))
    · have : False := by omega
      exact False.elim this
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hstd | hrest
    · subst hstd
      simp [standardDiagramEven_horizontalChild_threeRowTwoOneDiagramEven 3 (by omega)]
    rcases hrest with h22 | h211
    · subst h22
      simp [twoRowTwoDiagramEven_horizontalChild_threeRowTwoOneDiagramEven 3 (by omega)]
    · subst h211
      simp [twoRowOneOneDiagramEven_horizontalChild_threeRowTwoOneDiagramEven 3 (by omega)]

/-- Horizontal children of `(2m-3,2,1)` for `m ≥ 4`, as a concrete Finset. -/
theorem horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 4 ≤ m) :
    horizontalTwoStripChildrenEven m (threeRowTwoOneDiagramEven m (by omega)) =
      {standardDiagramEven (m - 1) (by omega),
        twoRowTwoDiagramEven (m - 1) (by omega),
        twoRowOneOneDiagramEven (m - 1) (by omega),
        threeRowTwoOneDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (threeRowTwoOneDiagramEven m (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases horizontalChild_threeRowTwoOneDiagramEven_classification m hm mu hstrip with
      hstd | hrest
    · exact Finset.mem_insert.mpr (Or.inl hstd)
    rcases hrest with h22 | hrest
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl h22)))
    rcases hrest with h211 | h321
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl h211)))))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr h321))))))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hmu
    unfold horizontalTwoStripChildrenEven
    rcases hmu with hstd | hrest
    · subst hstd
      simp [standardDiagramEven_horizontalChild_threeRowTwoOneDiagramEven m (by omega)]
    rcases hrest with h22 | hrest
    · subst h22
      simp [twoRowTwoDiagramEven_horizontalChild_threeRowTwoOneDiagramEven m (by omega)]
    rcases hrest with h211 | h321
    · subst h211
      simp [twoRowOneOneDiagramEven_horizontalChild_threeRowTwoOneDiagramEven m (by omega)]
    · subst h321
      simp [threeRowTwoOneDiagramEven_horizontalChild_threeRowTwoOneDiagramEven m hm]

/-- Vertical children of `(2m-3,2,1)` are standard, `(2m-4,2)`,
or `(2m-4,1,1)`. -/
theorem verticalChild_threeRowTwoOneDiagramEven_classification
    (m : ℕ) (hm : 3 ≤ m) (mu : YoungDiagram (2 * (m - 1)))
    (hstrip :
      IsVerticalTwoStripChild (threeRowTwoOneDiagramEven m hm) mu) :
    mu = standardDiagramEven (m - 1) (by omega) ∨
      mu = twoRowTwoDiagramEven (m - 1) (by omega) ∨
        mu = twoRowOneOneDiagramEven (m - 1) (by omega) := by
  have htail : ∀ {i : ℕ}, 3 ≤ i → youngRow mu i = 0 := by
    intro i hi
    by_cases hin : i < 2 * (m - 1)
    · let ib : Fin (2 * m) := Fin.mk i (by omega)
      have hsub := hstrip.2.1 ib
      have hparent : youngRow (threeRowTwoOneDiagramEven m hm) i = 0 := by
        unfold threeRowTwoOneDiagramEven
        rw [youngRow_threeRowDiagram]
        have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        have hi2 : i ≠ 2 := by omega
        simp [hi0, hi1, hi2]
      have hle0 : youngRow mu i ≤ 0 := by
        simpa [ib, hparent] using hsub
      omega
    · unfold youngRow
      simp [hin]
  have hsum012 :
      youngRow mu 0 + youngRow mu 1 + youngRow mu 2 = 2 * (m - 1) := by
    exact youngRow_zero_add_one_add_two_eq_size_of_tail_zero
      (by omega : 3 ≤ 2 * (m - 1)) mu htail
  have hmu0_ge : 2 * m - 4 ≤ youngRow mu 0 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hle := hstrip.2.2 i0
    have hparent : youngRow (threeRowTwoOneDiagramEven m hm) 0 = 2 * m - 3 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m hm).1
    have hle' : 2 * m - 3 ≤ youngRow mu 0 + 1 := by
      simpa [i0, hparent] using hle
    omega
  have hmu0_le : youngRow mu 0 ≤ 2 * m - 3 := by
    let i0 : Fin (2 * m) := Fin.mk 0 (by omega)
    have hsub := hstrip.2.1 i0
    have hparent : youngRow (threeRowTwoOneDiagramEven m hm) 0 = 2 * m - 3 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m hm).1
    simpa [i0, hparent] using hsub
  have hmu1_ge : 1 ≤ youngRow mu 1 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hle := hstrip.2.2 i1
    have hparent : youngRow (threeRowTwoOneDiagramEven m hm) 1 = 2 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m hm).2.1
    have hle' : 2 ≤ youngRow mu 1 + 1 := by
      simpa [i1, hparent] using hle
    omega
  have hmu1_le : youngRow mu 1 ≤ 2 := by
    let i1 : Fin (2 * m) := Fin.mk 1 (by omega)
    have hsub := hstrip.2.1 i1
    have hparent : youngRow (threeRowTwoOneDiagramEven m hm) 1 = 2 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m hm).2.1
    simpa [i1, hparent] using hsub
  have hmu2_le : youngRow mu 2 ≤ 1 := by
    let i2 : Fin (2 * m) := Fin.mk 2 (by omega)
    have hsub := hstrip.2.1 i2
    have hparent : youngRow (threeRowTwoOneDiagramEven m hm) 2 = 1 :=
      (isThreeRowTwoOneException_threeRowTwoOneDiagramEven m hm).2.2
    simpa [i2, hparent] using hsub
  have hmu0_cases :
      youngRow mu 0 = 2 * m - 3 ∨ youngRow mu 0 = 2 * m - 4 := by
    omega
  rcases hmu0_cases with hmu0 | hmu0
  · left
    have hmu1 : youngRow mu 1 = 1 := by omega
    apply eq_standardDiagramEven_of_isStandard (m - 1) (by omega)
    unfold IsStandard
    constructor
    · omega
    constructor
    · omega
    · exact hmu1
  · have hmu1_cases : youngRow mu 1 = 1 ∨ youngRow mu 1 = 2 := by omega
    rcases hmu1_cases with hmu1 | hmu1
    · right
      right
      have hmu2 : youngRow mu 2 = 1 := by omega
      apply eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException (m - 1) (by omega)
      unfold IsTwoRowOneOneException
      constructor
      · omega
      constructor
      · exact hmu1
      · exact hmu2
    · right
      left
      apply eq_twoRowTwoDiagramEven_of_isTwoRowTwoException (m - 1) (by omega)
      unfold IsTwoRowTwoException
      constructor
      · omega
      · exact hmu1

/-- Vertical children of `(2m-3,2,1)`, as a concrete Finset. -/
theorem verticalTwoStripChildrenEven_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    verticalTwoStripChildrenEven m (threeRowTwoOneDiagramEven m hm) =
      {standardDiagramEven (m - 1) (by omega),
        twoRowTwoDiagramEven (m - 1) (by omega),
        twoRowOneOneDiagramEven (m - 1) (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsVerticalTwoStripChild (threeRowTwoOneDiagramEven m hm) mu :=
      (Finset.mem_filter.mp hmu).2
    rcases verticalChild_threeRowTwoOneDiagramEven_classification m hm mu hstrip with
      hstd | hrest
    · exact Finset.mem_insert.mpr (Or.inl hstd)
    rcases hrest with h22 | h211
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl h22)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr h211))))
  · intro hmu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmu
    unfold verticalTwoStripChildrenEven
    rcases hmu with hstd | hrest
    · subst hstd
      simp [standardDiagramEven_verticalChild_threeRowTwoOneDiagramEven m hm]
    rcases hrest with h22 | h211
    · subst h22
      simp [twoRowTwoDiagramEven_verticalChild_threeRowTwoOneDiagramEven m hm]
    · subst h211
      simp [twoRowOneOneDiagramEven_verticalChild_threeRowTwoOneDiagramEven m hm]

/-- If the one-row diagram occurs vertically, the only nonstandard possibility
is `(2m-2,1,1)`.

This is the second case of the paper's "where the induction can fail" lemma. -/
theorem hasOneRowVerticalChild_classification
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hstd : ¬ IsStandard lam) (hchild : HasOneRowVerticalChild m lam) :
    IsTwoRowOneOneException m lam := by
  classical
  rcases hchild with ⟨mu, hmu, hone⟩
  have hstrip : IsVerticalTwoStripChild lam mu := (Finset.mem_filter.mp hmu).2
  let i0 : Fin (2 * m) := ⟨0, by omega⟩
  let i1 : Fin (2 * m) := ⟨1, by omega⟩
  let i2 : Fin (2 * m) := ⟨2, by omega⟩
  have hmu0 : youngRow mu 0 = 2 * m - 2 := by
    rw [hone]
    omega
  have hmu1 : youngRow mu 1 = 0 :=
    youngRow_eq_zero_of_isOneRow mu hone (by omega)
  have hmu2 : youngRow mu 2 = 0 :=
    youngRow_eq_zero_of_isOneRow mu hone (by omega)
  have h0_lower : 2 * m - 2 ≤ youngRow lam 0 := by
    have h := hstrip.2.1 i0
    simpa [i0, hmu0] using h
  have h0_upper : youngRow lam 0 ≤ 2 * m - 1 := by
    have h := hstrip.2.2 i0
    have hraw : youngRow lam 0 ≤ 2 * m - 2 + 1 := by
      simpa [i0, hmu0] using h
    omega
  have h1_upper : youngRow lam 1 ≤ 1 := by
    have h := hstrip.2.2 i1
    simpa [i1, hmu1] using h
  have h2_upper : youngRow lam 2 ≤ 1 := by
    have h := hstrip.2.2 i2
    simpa [i2, hmu2] using h
  have h0_cases :
      youngRow lam 0 = 2 * m - 2 ∨ youngRow lam 0 = 2 * m - 1 := by
    omega
  rcases h0_cases with h0 | h0
  · have h1 : youngRow lam 1 = 1 := by
      have hcases : youngRow lam 1 = 0 ∨ youngRow lam 1 = 1 := by
        omega
      rcases hcases with h1zero | h1one
      · have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow lam i = 0 := by
          intro i hi
          exact youngRow_eq_zero_of_one_le_of_youngRow_one_eq_zero
            (by omega : 1 < 2 * m) lam h1zero (by omega : 1 ≤ i)
        have hsum01 :=
          youngRow_zero_add_one_eq_size_of_tail_zero
            (by omega : 2 ≤ 2 * m) lam htail
        omega
      · exact h1one
    have h2 : youngRow lam 2 = 1 := by
      have hcases : youngRow lam 2 = 0 ∨ youngRow lam 2 = 1 := by
        omega
      rcases hcases with h2zero | h2one
      · have hsum01 :=
          youngRow_zero_add_one_eq_size_of_youngRow_two_eq_zero
            (by omega : 3 ≤ 2 * m) lam h2zero
        omega
      · exact h2one
    exact ⟨h0, h1, h2⟩
  · have h1 : youngRow lam 1 = 1 := by
      have hcases : youngRow lam 1 = 0 ∨ youngRow lam 1 = 1 := by
        omega
      rcases hcases with h1zero | h1one
      · have htail : ∀ {i : ℕ}, 2 ≤ i → youngRow lam i = 0 := by
          intro i hi
          exact youngRow_eq_zero_of_one_le_of_youngRow_one_eq_zero
            (by omega : 1 < 2 * m) lam h1zero (by omega : 1 ≤ i)
        have hsum01 :=
          youngRow_zero_add_one_eq_size_of_tail_zero
            (by omega : 2 ≤ 2 * m) lam htail
        omega
      · exact h1one
    have hstd' : IsStandard lam := by
      unfold IsStandard
      exact ⟨by omega, h0, h1⟩
    exact False.elim (hstd hstd')

/-- If the standard diagram occurs horizontally, the non-one-row, nonstandard
possibilities are exactly the four exceptional even shapes.

This is the third case of the paper's "where the induction can fail" lemma. -/
theorem hasStandardHorizontalChild_classification
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (_hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hchild : HasStandardHorizontalChild m lam) :
    IsEvenHExceptional m lam := by
  classical
  rcases hchild with ⟨mu, hmu, hmustd⟩
  have hstrip : IsHorizontalTwoStripChild lam mu := (Finset.mem_filter.mp hmu).2
  let i0 : Fin (2 * m) := ⟨0, by omega⟩
  let i1 : Fin (2 * m) := ⟨1, by omega⟩
  have hmu0 : youngRow mu 0 = 2 * m - 3 := by
    have h := hmustd.2.1
    rw [h]
    omega
  have hmu1 : youngRow mu 1 = 1 := hmustd.2.2
  have hmu_sum01 : youngRow mu 0 + youngRow mu 1 = 2 * (m - 1) := by
    rw [hmu0, hmu1]
    omega
  have hmu_tail : ∀ {i : ℕ}, 2 ≤ i → youngRow mu i = 0 := by
    intro i hi
    exact youngRow_eq_zero_of_two_le_of_first_two_sum
      (by omega : 2 ≤ 2 * (m - 1)) mu hmu_sum01 hi
  have h0_lower : 2 * m - 3 ≤ youngRow lam 0 := by
    have h := hstrip.2.1 i0
    simpa [i0, hmu0] using h
  have h1_lower : 1 ≤ youngRow lam 1 := by
    have h := hstrip.2.1 i1
    simpa [i1, hmu1] using h
  have h2_upper : youngRow lam 2 ≤ 1 := by
    have h := hstrip.2.2 i1
    simpa [i1, hmu1] using h
  have htail_lam : ∀ {i : ℕ}, 3 ≤ i → youngRow lam i = 0 := by
    intro i hi
    by_cases hin : i < 2 * m
    · let iprev : Fin (2 * m) := ⟨i - 1, by omega⟩
      have h := hstrip.2.2 iprev
      have hpred : i - 1 + 1 = i := by omega
      have hmu_zero : youngRow mu (i - 1) = 0 :=
        hmu_tail (by omega : 2 ≤ i - 1)
      have hle0 : youngRow lam i ≤ 0 := by
        simpa [iprev, hpred, hmu_zero] using h
      omega
    · unfold youngRow
      simp [hin]
  have hsum012 :
      youngRow lam 0 + youngRow lam 1 + youngRow lam 2 = 2 * m :=
    youngRow_zero_add_one_add_two_eq_size_of_tail_zero
      (by omega : 3 ≤ 2 * m) lam htail_lam
  have h0_cases :
      youngRow lam 0 = 2 * m - 3 ∨
        youngRow lam 0 = 2 * m - 2 ∨
          youngRow lam 0 = 2 * m - 1 := by
    omega
  rcases h0_cases with h0 | h0rest
  · have h2_cases : youngRow lam 2 = 0 ∨ youngRow lam 2 = 1 := by omega
    rcases h2_cases with h2 | h2
    · have h1 : youngRow lam 1 = 3 := by omega
      exact Or.inr (Or.inr (Or.inl ⟨h0, h1⟩))
    · have h1 : youngRow lam 1 = 2 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨h0, h1, h2⟩))
  rcases h0rest with h0 | h0
  · have h2_cases : youngRow lam 2 = 0 ∨ youngRow lam 2 = 1 := by omega
    rcases h2_cases with h2 | h2
    · have h1 : youngRow lam 1 = 2 := by omega
      exact Or.inl ⟨h0, h1⟩
    · have h1 : youngRow lam 1 = 1 := by omega
      exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
  · have h1 : youngRow lam 1 = 1 := by omega
    have hstd' : IsStandard lam := by
      unfold IsStandard
      exact ⟨by omega, h0, h1⟩
    exact False.elim (hstd hstd')

/-- Paper classification of all ways the generic even induction can fail. -/
theorem even_bad_child_classification
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam)
    (hbad :
      HasOneRowHorizontalChild m lam ∨
        HasOneRowVerticalChild m lam ∨
          HasStandardHorizontalChild m lam) :
    IsEvenHExceptional m lam := by
  rcases hbad with hHrow | hrest
  · rcases hasOneRowHorizontalChild_classification m (by omega) lam hrow hHrow with
      hstd' | htwo
    · exact False.elim (hstd hstd')
    · exact Or.inl htwo
  rcases hrest with hVrow | hHstd
  · exact Or.inr (Or.inl
      (hasOneRowVerticalChild_classification m hm lam hstd hVrow))
  · exact hasStandardHorizontalChild_classification m hm lam hrow hstd hHstd

/-!
## Tableau-dimension even certificate layer

The original `hEven` recurrence in `Defs.lean` is tied to the hook-length proxy
`youngDim`.  The tableau-count migration therefore uses a parallel recurrence
where the vertical contribution is `tableauDim μ - zEven μ`.
-/

theorem hEvenTableau_recurrence_succ
    (m : ℕ) (lam : YoungDiagram (2 * (m + 1))) :
    hEvenTableau (m + 1) lam =
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => hEvenTableau m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu - zEven m mu) := by
  simp [hEvenTableau]

/-- Generic tableau-dimension induction step for Lemma 5.25, away from the
exceptional children. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_generic_step_succ
    (m : ℕ) (_hm : 1 ≤ m) (lam : YoungDiagram (2 * (m + 1)))
    (ih :
      ∀ mu : YoungDiagram (2 * m),
        ¬ IsOneRow mu → ¬ IsStandard mu →
          (1 / 5 : ℝ) * tableauDim mu ≤ hEvenTableau m mu)
    (hHrow :
      ∀ mu ∈ horizontalTwoStripChildrenEven (m + 1) lam, ¬ IsOneRow mu)
    (hHstd :
      ∀ mu ∈ horizontalTwoStripChildrenEven (m + 1) lam, ¬ IsStandard mu)
    (hVrow :
      ∀ mu ∈ verticalTwoStripChildrenEven (m + 1) lam, ¬ IsOneRow mu) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau (m + 1) lam := by
  classical
  have hhrec := hEvenTableau_recurrence_succ m lam
  have hdimrec := tableauDim_twoStripChildrenEven_branching_succ m lam
  have hH :
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => (1 / 5 : ℝ) * tableauDim mu) ≤
        (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => hEvenTableau m mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    exact ih mu (hHrow mu hmu) (hHstd mu hmu)
  have hV :
      (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => (1 / 5 : ℝ) * tableauDim mu) ≤
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => tableauDim mu - zEven m mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    have hz :
        zEven m mu ≤ (1 / 2 : ℝ) * tableauDim mu :=
      zEven_le_half_tableauDim_of_not_oneRow_finite_induction
        m mu (hVrow mu hmu)
    have hdim_nonneg : 0 ≤ tableauDim mu := tableauDim_nonneg mu
    nlinarith
  calc
    (1 / 5 : ℝ) * tableauDim lam
        = (horizontalTwoStripChildrenEven (m + 1) lam).sum
              (fun mu => (1 / 5 : ℝ) * tableauDim mu) +
            (verticalTwoStripChildrenEven (m + 1) lam).sum
              (fun mu => (1 / 5 : ℝ) * tableauDim mu) := by
          rw [hdimrec]
          rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    _ ≤
        (horizontalTwoStripChildrenEven (m + 1) lam).sum
            (fun mu => hEvenTableau m mu) +
          (verticalTwoStripChildrenEven (m + 1) lam).sum
            (fun mu => tableauDim mu - zEven m mu) := by
          exact add_le_add hH hV
    _ = hEvenTableau (m + 1) lam := by rw [hhrec]

/-- One-row shapes have no high local character weight in the tableau-count
recurrence. -/
theorem hEvenTableau_oneRowDiagram (m : ℕ) :
    hEvenTableau m (oneRowDiagram (2 * m)) = 0 := by
  induction m with
  | zero =>
      simp [hEvenTableau]
  | succ m ih =>
      rw [hEvenTableau]
      rw [horizontalTwoStripChildrenEven_oneRowDiagram (m + 1) (by omega)]
      rw [verticalTwoStripChildrenEven_oneRowDiagram (m + 1) (by omega)]
      rw [Finset.sum_singleton]
      rw [Finset.sum_empty]
      simp [ih]

/-- Standard shapes also have no high local character weight in the
tableau-count recurrence. -/
theorem hEvenTableau_standardDiagramEven_formula
    (m : ℕ) (hm : 1 ≤ m) :
    hEvenTableau m (standardDiagramEven m hm) = 0 := by
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
          rw [hEvenTableau]
          rw [horizontalTwoStripChildrenEven_standardDiagramEven_one_tableauBase]
          rw [verticalTwoStripChildrenEven_standardDiagramEven_one_tableauBase]
          have hempty :
              Finset.sum
                  (Finset.empty : Finset (YoungDiagram (2 * (1 - 1))))
                  (fun mu => hEvenTableau 0 mu) = 0 := by
            exact Finset.sum_empty
          rw [hempty]
          rw [Finset.sum_singleton]
          rw [tableauDim_oneRowDiagram_zero]
          simp [zEven]
      | succ k =>
          have hm2 : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hshape :
              standardDiagramEven (Nat.succ (Nat.succ k)) hm =
                standardDiagramEven (Nat.succ (Nat.succ k)) (by omega) := by
            exact standardDiagramEven_proof_irrel _ hm (by omega)
          rw [hshape]
          rw [hEvenTableau]
          have hh :=
            horizontalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          have hv :=
            verticalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          rw [hh, hv]
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
          change
            ({a, b} :
                Finset
                  (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                (fun mu => hEvenTableau (Nat.succ k) mu) +
              ({a} :
                Finset
                  (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                (fun mu => tableauDim mu - zEven (Nat.succ k) mu) = 0
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          dsimp [a, b]
          change
            hEvenTableau (Nat.succ k)
                (oneRowDiagram (2 * Nat.succ k)) +
              hEvenTableau (Nat.succ k)
                (standardDiagramEven (Nat.succ k) (by omega)) +
              (tableauDim (oneRowDiagram (2 * Nat.succ k)) -
                zEven (Nat.succ k) (oneRowDiagram (2 * Nat.succ k))) = 0
          rw [hEvenTableau_oneRowDiagram]
          rw [ih (by omega : 1 ≤ Nat.succ k)]
          rw [tableauDim_oneRowDiagram_even]
          rw [zEven_oneRowDiagram]
          ring

/-- The tableau-count high-weight recurrence is nonnegative. -/
theorem hEvenTableau_nonneg
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    0 ≤ hEvenTableau m lam := by
  induction m with
  | zero =>
      simp [hEvenTableau]
  | succ m ih =>
      rw [hEvenTableau]
      apply add_nonneg
      · exact Finset.sum_nonneg (fun mu _hmu => ih mu)
      · exact Finset.sum_nonneg (fun mu _hmu =>
          sub_nonneg.mpr (zEven_le_tableauDim m mu))

/-- Formula for `hEvenTableau` on the canonical two-row exception
`(2m-2,2)`. -/
theorem hEvenTableau_twoRowTwoDiagramEven_formula
    (m : ℕ) (hm : 2 ≤ m) :
    hEvenTableau m (twoRowTwoDiagramEven m hm) =
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
              rw [twoRowTwoDiagramEven_proof_irrel 2 hm (by omega)]
              rw [hEvenTableau]
              rw [horizontalTwoStripChildrenEven_twoRowTwoDiagramEven_two]
              rw [verticalTwoStripChildrenEven_twoRowTwoDiagramEven 2 (by omega)]
              rw [Finset.sum_singleton]
              rw [Finset.sum_singleton]
              rw [hEvenTableau_oneRowDiagram]
              rw [tableauDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num
          | succ k =>
              have hm3 :
                  3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              rw [twoRowTwoDiagramEven_proof_irrel
                (Nat.succ (Nat.succ (Nat.succ k))) hm (by omega)]
              rw [hEvenTableau]
              have hh :=
                horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
              rw [hh, hv]
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
              change
                ({a, b, c} :
                    Finset
                      (YoungDiagram
                        (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => hEvenTableau (Nat.succ (Nat.succ k)) mu) +
                  ({b} :
                    Finset
                      (YoungDiagram
                        (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu =>
                      tableauDim mu - zEven (Nat.succ (Nat.succ k)) mu) =
                  ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                    (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                hEvenTableau (Nat.succ (Nat.succ k))
                    (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                  (hEvenTableau (Nat.succ (Nat.succ k))
                    (standardDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) +
                  hEvenTableau (Nat.succ (Nat.succ k))
                    (twoRowTwoDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega))) +
                  (tableauDim
                    (standardDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) -
                    zEven (Nat.succ (Nat.succ k))
                      (standardDiagramEven
                        (Nat.succ (Nat.succ k)) (by omega))) =
                  ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                    (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEvenTableau_oneRowDiagram]
              rw [hEvenTableau_standardDiagramEven_formula]
              have ihtwo := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ihtwo]
              rw [tableauDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

theorem hEvenTableau_ge_one_fifth_tableauDim_twoRowTwoException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowTwoException m lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m (by omega) lam hshape]
  rw [hEvenTableau_twoRowTwoDiagramEven_formula m (by omega)]
  rw [tableauDim_twoRowTwoDiagramEven_formula m (by omega)]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Formula for `hEvenTableau` on the canonical three-row exception
`(2m-2,1,1)`. -/
theorem hEvenTableau_twoRowOneOneDiagramEven_formula
    (m : ℕ) (hm : 2 ≤ m) :
    hEvenTableau m (twoRowOneOneDiagramEven m hm) =
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
              have hshape :
                  twoRowOneOneDiagramEven 2 hm =
                    twoRowOneOneDiagramEven 2 (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel 2 hm (by omega)
              rw [hshape]
              change
                hEvenTableau 2 (twoRowOneOneDiagramEven 2 (by omega)) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [hEvenTableau]
              rw [horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven_two]
              rw [verticalTwoStripChildrenEven_twoRowOneOneDiagramEven_two]
              let a : YoungDiagram (2 * (2 - 1)) := oneRowDiagram 2
              let b : YoungDiagram (2 * (2 - 1)) := standardDiagramEven 1 (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven 1 (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have ha_not : a ∉ ({b} : Finset (YoungDiagram (2 * (2 - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              change
                ({b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => hEvenTableau 1 mu) +
                  ({a, b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => tableauDim mu - zEven 1 mu) =
                    (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b]
              change
                hEvenTableau 1 (standardDiagramEven 1 (by omega)) +
                  ((tableauDim (oneRowDiagram (2 * 1)) -
                    zEven 1 (oneRowDiagram (2 * 1))) +
                    (tableauDim (standardDiagramEven 1 (by omega)) -
                      zEven 1 (standardDiagramEven 1 (by omega)))) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [hEvenTableau_standardDiagramEven_formula]
              rw [tableauDim_oneRowDiagram_even]
              rw [zEven_oneRowDiagram]
              rw [tableauDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hshape :
                  twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) hm =
                    twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel _ hm (by omega)
              rw [hshape]
              change
                hEvenTableau (Nat.succ (Nat.succ (Nat.succ k)))
                  (twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) (by omega)) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEvenTableau]
              have hh :=
                horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              rw [hh, hv]
              let a : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowOneOneDiagramEven
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
              have hbc : b ≠ c := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 2) h
                have hb2 : youngRow b 2 = 0 := by
                  dsimp [b]
                  unfold standardDiagramEven
                  rw [youngRow_twoRowDiagram]
                  simp
                have hc2 : youngRow c 2 = 1 := by
                  dsimp [c]
                  exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hbc hmem
              have ha_not :
                  a ∉ ({b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              change
                ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => hEvenTableau (Nat.succ (Nat.succ k)) mu) +
                  ({a, b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => tableauDim mu - zEven (Nat.succ (Nat.succ k)) mu) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                hEvenTableau (Nat.succ (Nat.succ k))
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  hEvenTableau (Nat.succ (Nat.succ k))
                    (twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) +
                  ((tableauDim (oneRowDiagram (2 * Nat.succ (Nat.succ k))) -
                    zEven (Nat.succ (Nat.succ k))
                      (oneRowDiagram (2 * Nat.succ (Nat.succ k)))) +
                    (tableauDim
                        (standardDiagramEven
                          (Nat.succ (Nat.succ k)) (by omega)) -
                      zEven (Nat.succ (Nat.succ k))
                        (standardDiagramEven
                          (Nat.succ (Nat.succ k)) (by omega)))) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEvenTableau_standardDiagramEven_formula]
              have ih211 := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ih211]
              rw [tableauDim_oneRowDiagram_even]
              rw [zEven_oneRowDiagram]
              rw [tableauDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- Dimension formula for the canonical three-row exception `(2m-2,1,1)`,
using actual tableau counts. -/
theorem tableauDim_twoRowOneOneDiagramEven_formula
    (m : ℕ) (hm : 2 ≤ m) :
    tableauDim (twoRowOneOneDiagramEven m hm) =
      (2 * (m : ℝ) - 1) * ((m : ℝ) - 1) := by
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
              have hshape :
                  twoRowOneOneDiagramEven 2 hm =
                    twoRowOneOneDiagramEven 2 (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel 2 hm (by omega)
              rw [hshape]
              change
                tableauDim (twoRowOneOneDiagramEven 2 (by omega)) =
                  (2 * (2 : ℝ) - 1) * ((2 : ℝ) - 1)
              have hrec :=
                tableauDim_twoStripChildrenEven_branching_succ
                  1 (twoRowOneOneDiagramEven 2 (by omega))
              rw [horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven_two] at hrec
              rw [verticalTwoStripChildrenEven_twoRowOneOneDiagramEven_two] at hrec
              let a : YoungDiagram (2 * (2 - 1)) := oneRowDiagram 2
              let b : YoungDiagram (2 * (2 - 1)) := standardDiagramEven 1 (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven 1 (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have ha_not : a ∉ ({b} : Finset (YoungDiagram (2 * (2 - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              rw [hrec]
              change
                ({b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => tableauDim mu) +
                  ({a, b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => tableauDim mu) =
                  (2 * (2 : ℝ) - 1) * ((2 : ℝ) - 1)
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b]
              have hone : tableauDim (oneRowDiagram 2) = 1 := by
                change tableauDim (oneRowDiagram (2 * 1)) = 1
                rw [tableauDim_oneRowDiagram_even]
              rw [hone]
              rw [tableauDim_standardDiagramEven_formula]
              norm_num
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hshape :
                  twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) hm =
                    twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel _ hm (by omega)
              rw [hshape]
              have hrec :=
                tableauDim_twoStripChildrenEven_branching_succ
                  (Nat.succ (Nat.succ k))
                  (twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) (by omega))
              have hh :=
                horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              rw [hh, hv] at hrec
              let a : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowOneOneDiagramEven
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
              have hbc : b ≠ c := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 2) h
                have hb2 : youngRow b 2 = 0 := by
                  dsimp [b]
                  unfold standardDiagramEven
                  rw [youngRow_twoRowDiagram]
                  simp
                have hc2 : youngRow c 2 = 1 := by
                  dsimp [c]
                  exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hbc hmem
              have ha_not :
                  a ∉ ({b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              rw [hrec]
              change
                ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => tableauDim mu) +
                  ({a, b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => tableauDim mu) =
                    (2 * ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1)
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                tableauDim
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  tableauDim
                    (twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) +
                  (tableauDim (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                    tableauDim
                      (standardDiagramEven
                        (Nat.succ (Nat.succ k)) (by omega))) =
                    (2 * ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1)
              rw [tableauDim_standardDiagramEven_formula]
              have ih211 := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ih211]
              rw [tableauDim_oneRowDiagram_even]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

theorem hEvenTableau_ge_one_fifth_tableauDim_twoRowOneOneException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowOneOneException m lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  rw [eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException m (by omega) lam hshape]
  rw [hEvenTableau_twoRowOneOneDiagramEven_formula m (by omega)]
  rw [tableauDim_twoRowOneOneDiagramEven_formula m (by omega)]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Recursive exceptional check for the canonical shape `(2m-3,3)`, using
actual tableau counts. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_twoRowThreeDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    (1 / 5 : ℝ) * tableauDim (twoRowThreeDiagramEven m hm) ≤
      hEvenTableau m (twoRowThreeDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_two : m = 2
      · subst m
        have hshape :
            twoRowThreeDiagramEven 3 hm =
              twoRowThreeDiagramEven 3 (by omega) := by
          exact twoRowThreeDiagramEven_proof_irrel 3 hm (by omega)
        rw [hshape]
        have hdim :
            tableauDim (twoRowThreeDiagramEven 3 (by omega)) = 5 := by
          have hrec :=
            tableauDim_twoStripChildrenEven_branching_succ
              2 (twoRowThreeDiagramEven 3 (by omega))
          rw [horizontalTwoStripChildrenEven_twoRowThreeDiagramEven_three] at hrec
          rw [verticalTwoStripChildrenEven_twoRowThreeDiagramEven 3 (by omega)] at hrec
          rw [hrec]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          rw [tableauDim_standardDiagramEven_formula]
          rw [tableauDim_twoRowTwoDiagramEven_formula]
          norm_num
        rw [hdim]
        rw [hEvenTableau]
        rw [horizontalTwoStripChildrenEven_twoRowThreeDiagramEven_three]
        rw [verticalTwoStripChildrenEven_twoRowThreeDiagramEven 3 (by omega)]
        rw [Finset.sum_singleton]
        rw [Finset.sum_singleton]
        rw [hEvenTableau_standardDiagramEven_formula]
        rw [tableauDim_twoRowTwoDiagramEven_formula]
        rw [zEven_twoRowTwoDiagramEven_formula]
        norm_num
      · have hm4 : 4 ≤ Nat.succ m := by omega
        have hmprev : 3 ≤ m := by omega
        have hshape :
            twoRowThreeDiagramEven (Nat.succ m) hm =
              twoRowThreeDiagramEven (Nat.succ m) (by omega) := by
          exact twoRowThreeDiagramEven_proof_irrel (Nat.succ m) hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (Nat.succ m - 1)) :=
          standardDiagramEven (Nat.succ m - 1) (by omega)
        let b : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowTwoDiagramEven (Nat.succ m - 1) (by omega)
        let c : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowThreeDiagramEven (Nat.succ m - 1) (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 3 := by
            dsimp [c]
            exact (isTwoRowThreeException_twoRowThreeDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 3 := by
            dsimp [c]
            exact (isTwoRowThreeException_twoRowThreeDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          omega
        have ha_not :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not :
            b ∉ ({c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh :=
          horizontalTwoStripChildrenEven_twoRowThreeDiagramEven
            (Nat.succ m) hm4
        have hv :=
          verticalTwoStripChildrenEven_twoRowThreeDiagramEven
            (Nat.succ m) (by omega)
        have hdimrec :=
          tableauDim_twoStripChildrenEven_branching_succ
            m (twoRowThreeDiagramEven (Nat.succ m) (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            tableauDim (twoRowThreeDiagramEven (Nat.succ m) (by omega)) =
              tableauDim a + tableauDim b + tableauDim c + tableauDim b := by
          rw [hdimrec]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu) +
              ({b} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu) =
              tableauDim a + tableauDim b + tableauDim c + tableauDim b
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEvenTableau (Nat.succ m)
                (twoRowThreeDiagramEven (Nat.succ m) (by omega)) =
              hEvenTableau m a + hEvenTableau m b + hEvenTableau m c +
                (tableauDim b - zEven m b) := by
          rw [hEvenTableau]
          rw [hh, hv]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => hEvenTableau m mu) +
              ({b} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu - zEven m mu) =
              hEvenTableau m a + hEvenTableau m b + hEvenTableau m c +
                (tableauDim b - zEven m b)
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c]
        change
          (1 / 5 : ℝ) *
              (tableauDim (standardDiagramEven m (by omega)) +
                tableauDim (twoRowTwoDiagramEven m (by omega)) +
                tableauDim (twoRowThreeDiagramEven m (by omega)) +
                tableauDim (twoRowTwoDiagramEven m (by omega))) ≤
            hEvenTableau m (standardDiagramEven m (by omega)) +
              hEvenTableau m (twoRowTwoDiagramEven m (by omega)) +
              hEvenTableau m (twoRowThreeDiagramEven m (by omega)) +
              (tableauDim (twoRowTwoDiagramEven m (by omega)) -
                zEven m (twoRowTwoDiagramEven m (by omega)))
        rw [hEvenTableau_standardDiagramEven_formula]
        rw [hEvenTableau_twoRowTwoDiagramEven_formula]
        rw [tableauDim_standardDiagramEven_formula]
        rw [tableauDim_twoRowTwoDiagramEven_formula]
        rw [zEven_twoRowTwoDiagramEven_formula]
        have ihc := ih hmprev
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hmprev
        nlinarith

theorem hEvenTableau_ge_one_fifth_tableauDim_twoRowThreeException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowThreeException m lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  rw [eq_twoRowThreeDiagramEven_of_isTwoRowThreeException m hm lam hshape]
  exact hEvenTableau_ge_one_fifth_tableauDim_twoRowThreeDiagramEven m hm

/-- Recursive exceptional check for the canonical shape `(2m-3,2,1)`, using
actual tableau counts. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_threeRowTwoOneDiagramEven
    (m : ℕ) (hm : 3 ≤ m) :
    (1 / 5 : ℝ) * tableauDim (threeRowTwoOneDiagramEven m hm) ≤
      hEvenTableau m (threeRowTwoOneDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_two : m = 2
      · subst m
        have hshape :
            threeRowTwoOneDiagramEven 3 hm =
              threeRowTwoOneDiagramEven 3 (by omega) := by
          exact threeRowTwoOneDiagramEven_proof_irrel 3 hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (3 - 1)) := standardDiagramEven 2 (by omega)
        let b : YoungDiagram (2 * (3 - 1)) := twoRowTwoDiagramEven 2 (by omega)
        let c : YoungDiagram (2 * (3 - 1)) := twoRowOneOneDiagramEven 2 (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven 2 (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven 2 (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hc2 : youngRow c 2 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.2
          have ha2 : youngRow a 2 = 0 := by
            dsimp [a]
            unfold standardDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.1
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven 2 (by omega)).2
          omega
        have ha_not :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (3 - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not :
            b ∉ ({c} : Finset (YoungDiagram (2 * (3 - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh := horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven_three
        have hv := verticalTwoStripChildrenEven_threeRowTwoOneDiagramEven 3 (by omega)
        have hdimrec :=
          tableauDim_twoStripChildrenEven_branching_succ
            2 (threeRowTwoOneDiagramEven 3 (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            tableauDim (threeRowTwoOneDiagramEven 3 (by omega)) =
              (tableauDim a + tableauDim b + tableauDim c) +
                (tableauDim a + tableauDim b + tableauDim c) := by
          rw [hdimrec]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => tableauDim mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => tableauDim mu) =
              (tableauDim a + tableauDim b + tableauDim c) +
                (tableauDim a + tableauDim b + tableauDim c)
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEvenTableau 3 (threeRowTwoOneDiagramEven 3 (by omega)) =
              (hEvenTableau 2 a + hEvenTableau 2 b + hEvenTableau 2 c) +
                ((tableauDim a - zEven 2 a) +
                  (tableauDim b - zEven 2 b) +
                    (tableauDim c - zEven 2 c)) := by
          rw [hEvenTableau]
          rw [hh, hv]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => hEvenTableau 2 mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => tableauDim mu - zEven 2 mu) =
              (hEvenTableau 2 a + hEvenTableau 2 b + hEvenTableau 2 c) +
                ((tableauDim a - zEven 2 a) +
                  (tableauDim b - zEven 2 b) +
                    (tableauDim c - zEven 2 c))
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c]
        change
          (1 / 5 : ℝ) *
              ((tableauDim (standardDiagramEven 2 (by omega)) +
                  tableauDim (twoRowTwoDiagramEven 2 (by omega)) +
                    tableauDim (twoRowOneOneDiagramEven 2 (by omega))) +
                (tableauDim (standardDiagramEven 2 (by omega)) +
                  tableauDim (twoRowTwoDiagramEven 2 (by omega)) +
                    tableauDim (twoRowOneOneDiagramEven 2 (by omega)))) ≤
            (hEvenTableau 2 (standardDiagramEven 2 (by omega)) +
                hEvenTableau 2 (twoRowTwoDiagramEven 2 (by omega)) +
                  hEvenTableau 2 (twoRowOneOneDiagramEven 2 (by omega))) +
              ((tableauDim (standardDiagramEven 2 (by omega)) -
                  zEven 2 (standardDiagramEven 2 (by omega))) +
                (tableauDim (twoRowTwoDiagramEven 2 (by omega)) -
                  zEven 2 (twoRowTwoDiagramEven 2 (by omega))) +
                  (tableauDim (twoRowOneOneDiagramEven 2 (by omega)) -
                    zEven 2 (twoRowOneOneDiagramEven 2 (by omega))))
        rw [hEvenTableau_standardDiagramEven_formula]
        rw [hEvenTableau_twoRowTwoDiagramEven_formula]
        rw [hEvenTableau_twoRowOneOneDiagramEven_formula]
        have hza :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            2 (standardDiagramEven 2 (by omega))
            (not_isOneRow_standardDiagramEven 2 (by omega))
        have hzb :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            2 (twoRowTwoDiagramEven 2 (by omega))
            (not_isOneRow_twoRowTwoDiagramEven 2 (by omega))
        have hzc :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            2 (twoRowOneOneDiagramEven 2 (by omega))
            (not_isOneRow_twoRowOneOneDiagramEven 2 (by omega))
        have hda := tableauDim_nonneg (standardDiagramEven 2 (by omega))
        have hdb := tableauDim_nonneg (twoRowTwoDiagramEven 2 (by omega))
        have hdc := tableauDim_nonneg (twoRowOneOneDiagramEven 2 (by omega))
        norm_num
        nlinarith
      · have hm4 : 4 ≤ Nat.succ m := by omega
        have hmprev : 3 ≤ m := by omega
        have hshape :
            threeRowTwoOneDiagramEven (Nat.succ m) hm =
              threeRowTwoOneDiagramEven (Nat.succ m) (by omega) := by
          exact threeRowTwoOneDiagramEven_proof_irrel (Nat.succ m) hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (Nat.succ m - 1)) :=
          standardDiagramEven (Nat.succ m - 1) (by omega)
        let b : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowTwoDiagramEven (Nat.succ m - 1) (by omega)
        let c : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowOneOneDiagramEven (Nat.succ m - 1) (by omega)
        let d : YoungDiagram (2 * (Nat.succ m - 1)) :=
          threeRowTwoOneDiagramEven (Nat.succ m - 1) (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hc2 : youngRow c 2 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          have ha2 : youngRow a 2 = 0 := by
            dsimp [a]
            unfold standardDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hda : d ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hd1 : youngRow d 1 = 2 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          omega
        have hdb : d ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hd2 : youngRow d 2 = 1 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          have hb2 : youngRow b 2 = 0 := by
            dsimp [b]
            unfold twoRowTwoDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hdc : d ≠ c := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hd1 : youngRow d 1 = 2 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          omega
        have ha_not_h :
            a ∉ ({b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac | had
          · exact hba hab.symm
          · exact hca hac.symm
          · exact hda had.symm
        have hb_not_h :
            b ∉ ({c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hbc | hbd
          · exact hcb hbc.symm
          · exact hdb hbd.symm
        have hc_not_h :
            c ∉ ({d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hdc hmem.symm
        have ha_not_v :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not_v :
            b ∉ ({c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh :=
          horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven
            (Nat.succ m) hm4
        have hv :=
          verticalTwoStripChildrenEven_threeRowTwoOneDiagramEven
            (Nat.succ m) (by omega)
        have hdimrec :=
          tableauDim_twoStripChildrenEven_branching_succ
            m (threeRowTwoOneDiagramEven (Nat.succ m) (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            tableauDim (threeRowTwoOneDiagramEven (Nat.succ m) (by omega)) =
              (tableauDim a + tableauDim b + tableauDim c + tableauDim d) +
                (tableauDim a + tableauDim b + tableauDim c) := by
          rw [hdimrec]
          change
            ({a, b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu) =
              (tableauDim a + tableauDim b + tableauDim c + tableauDim d) +
                (tableauDim a + tableauDim b + tableauDim c)
          rw [Finset.sum_insert ha_not_h]
          rw [Finset.sum_insert hb_not_h]
          rw [Finset.sum_insert hc_not_h]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not_v]
          rw [Finset.sum_insert hb_not_v]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEvenTableau (Nat.succ m)
                (threeRowTwoOneDiagramEven (Nat.succ m) (by omega)) =
              (hEvenTableau m a + hEvenTableau m b + hEvenTableau m c +
                  hEvenTableau m d) +
                ((tableauDim a - zEven m a) +
                  (tableauDim b - zEven m b) +
                    (tableauDim c - zEven m c)) := by
          rw [hEvenTableau]
          rw [hh, hv]
          change
            ({a, b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => hEvenTableau m mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => tableauDim mu - zEven m mu) =
              (hEvenTableau m a + hEvenTableau m b + hEvenTableau m c +
                  hEvenTableau m d) +
                ((tableauDim a - zEven m a) +
                  (tableauDim b - zEven m b) +
                    (tableauDim c - zEven m c))
          rw [Finset.sum_insert ha_not_h]
          rw [Finset.sum_insert hb_not_h]
          rw [Finset.sum_insert hc_not_h]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not_v]
          rw [Finset.sum_insert hb_not_v]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c, d]
        change
          (1 / 5 : ℝ) *
              ((tableauDim (standardDiagramEven m (by omega)) +
                  tableauDim (twoRowTwoDiagramEven m (by omega)) +
                    tableauDim (twoRowOneOneDiagramEven m (by omega)) +
                      tableauDim (threeRowTwoOneDiagramEven m (by omega))) +
                (tableauDim (standardDiagramEven m (by omega)) +
                  tableauDim (twoRowTwoDiagramEven m (by omega)) +
                    tableauDim (twoRowOneOneDiagramEven m (by omega)))) ≤
            (hEvenTableau m (standardDiagramEven m (by omega)) +
                hEvenTableau m (twoRowTwoDiagramEven m (by omega)) +
                  hEvenTableau m (twoRowOneOneDiagramEven m (by omega)) +
                    hEvenTableau m (threeRowTwoOneDiagramEven m (by omega))) +
              ((tableauDim (standardDiagramEven m (by omega)) -
                  zEven m (standardDiagramEven m (by omega))) +
                (tableauDim (twoRowTwoDiagramEven m (by omega)) -
                  zEven m (twoRowTwoDiagramEven m (by omega))) +
                  (tableauDim (twoRowOneOneDiagramEven m (by omega)) -
                    zEven m (twoRowOneOneDiagramEven m (by omega))))
        rw [hEvenTableau_standardDiagramEven_formula]
        rw [hEvenTableau_twoRowTwoDiagramEven_formula]
        rw [hEvenTableau_twoRowOneOneDiagramEven_formula]
        have ihd := ih hmprev
        have hza :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            m (standardDiagramEven m (by omega))
            (not_isOneRow_standardDiagramEven m (by omega))
        have hzb :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            m (twoRowTwoDiagramEven m (by omega))
            (not_isOneRow_twoRowTwoDiagramEven m (by omega))
        have hzc :=
          zEven_le_half_tableauDim_of_not_oneRow_finite_induction
            m (twoRowOneOneDiagramEven m (by omega))
            (not_isOneRow_twoRowOneOneDiagramEven m (by omega))
        have hda_non := tableauDim_nonneg (standardDiagramEven m (by omega))
        have hdb_non := tableauDim_nonneg (twoRowTwoDiagramEven m (by omega))
        have hdc_non := tableauDim_nonneg (twoRowOneOneDiagramEven m (by omega))
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hmprev
        nlinarith

theorem hEvenTableau_ge_one_fifth_tableauDim_threeRowTwoOneException
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsThreeRowTwoOneException m lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  rw [eq_threeRowTwoOneDiagramEven_of_isThreeRowTwoOneException m hm lam hshape]
  exact hEvenTableau_ge_one_fifth_tableauDim_threeRowTwoOneDiagramEven m hm

/-- Generic induction step for Lemma 5.25, away from the exceptional children.

Horizontal children are handled by the induction hypothesis.  Vertical children
are handled by the proven `zEven ≤ d/2` bound, which gives the stronger
contribution `d - z ≥ d/2 ≥ d/5`. -/
theorem hEven_ge_one_fifth_youngDim_generic_step
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) (lam : YoungDiagram (2 * m))
    (ih :
      ∀ mu : YoungDiagram (2 * (m - 1)),
        ¬ IsOneRow mu → ¬ IsStandard mu →
          (1 / 5 : ℝ) * youngDim mu ≤ hEven (m - 1) mu)
    (hHrow :
      ∀ mu ∈ horizontalTwoStripChildrenEven m lam, ¬ IsOneRow mu)
    (hHstd :
      ∀ mu ∈ horizontalTwoStripChildrenEven m lam, ¬ IsStandard mu)
    (hVrow :
      ∀ mu ∈ verticalTwoStripChildrenEven m lam, ¬ IsOneRow mu) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  classical
  have hhrec :
      hEven m lam =
        (horizontalTwoStripChildrenEven m lam).sum
            (fun mu => hEven (m - 1) mu) +
          (verticalTwoStripChildrenEven m lam).sum
            (fun mu => youngDim mu - zEven (m - 1) mu) := by
    cases m with
    | zero => omega
    | succ m =>
        simp [hEven]
  have hdimrec := youngDim_twoStrip_recurrence m hm lam
  have hH :
      (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 5 : ℝ) * youngDim mu) ≤
        (horizontalTwoStripChildrenEven m lam).sum
          (fun mu => hEven (m - 1) mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    exact ih mu (hHrow mu hmu) (hHstd mu hmu)
  have hV :
      (verticalTwoStripChildrenEven m lam).sum
          (fun mu => (1 / 5 : ℝ) * youngDim mu) ≤
        (verticalTwoStripChildrenEven m lam).sum
          (fun mu => youngDim mu - zEven (m - 1) mu) := by
    apply Finset.sum_le_sum
    intro mu hmu
    have hz :
        zEven (m - 1) mu ≤ (1 / 2 : ℝ) * youngDim mu :=
      zEven_le_half_youngDim_of_not_oneRow_finite_induction
        (m - 1) mu (hVrow mu hmu)
    have hdim_nonneg : 0 ≤ youngDim mu := youngDim_nonneg mu
    nlinarith
  calc
    (1 / 5 : ℝ) * youngDim lam
        = (horizontalTwoStripChildrenEven m lam).sum
              (fun mu => (1 / 5 : ℝ) * youngDim mu) +
            (verticalTwoStripChildrenEven m lam).sum
              (fun mu => (1 / 5 : ℝ) * youngDim mu) := by
          rw [hdimrec]
          rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    _ ≤
        (horizontalTwoStripChildrenEven m lam).sum
            (fun mu => hEven (m - 1) mu) +
          (verticalTwoStripChildrenEven m lam).sum
            (fun mu => youngDim mu - zEven (m - 1) mu) := by
          exact add_le_add hH hV
    _ = hEven m lam := by rw [hhrec]

/-- The one-row shape has no high local character weight. -/
theorem hEven_oneRowDiagram (m : ℕ) :
    hEven m (oneRowDiagram (2 * m)) = 0 := by
  induction m with
  | zero =>
      simp [hEven]
  | succ m ih =>
      cases m with
      | zero =>
          change hEven 1 (oneRowDiagram (2 * 1)) = 0
          rw [hEven]
          rw [horizontalTwoStripChildrenEven_oneRowDiagram 1 (by omega)]
          rw [verticalTwoStripChildrenEven_oneRowDiagram 1 (by omega)]
          simp [hEven]
      | succ k =>
          change
            hEven (Nat.succ (Nat.succ k))
              (oneRowDiagram (2 * Nat.succ (Nat.succ k))) = 0
          rw [hEven]
          rw [horizontalTwoStripChildrenEven_oneRowDiagram
            (Nat.succ (Nat.succ k)) (by omega)]
          rw [verticalTwoStripChildrenEven_oneRowDiagram
            (Nat.succ (Nat.succ k)) (by omega)]
          change
            ({oneRowDiagram (2 * Nat.succ k)} :
                Finset (YoungDiagram (2 * Nat.succ k))).sum
                (fun mu => hEven (Nat.succ k) mu) +
              (∅ : Finset (YoungDiagram (2 * Nat.succ k))).sum
                (fun mu => youngDim mu - zEven (Nat.succ k) mu) = 0
          rw [Finset.sum_singleton]
          rw [Finset.sum_empty]
          rw [add_zero]
          exact ih

/-- The standard shape `(1,1)` has no horizontal two-strip child. -/
theorem horizontalTwoStripChildrenEven_standardDiagramEven_one :
    horizontalTwoStripChildrenEven 1 (standardDiagramEven 1 (by omega)) = ∅ := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip :
        IsHorizontalTwoStripChild (standardDiagramEven 1 (by omega)) mu :=
      (Finset.mem_filter.mp hmu).2
    let i0 : Fin (2 * 1) := ⟨0, by omega⟩
    have hle := hstrip.2.2 i0
    have hparent : youngRow (standardDiagramEven 1 (by omega)) 1 = 1 :=
      (isStandard_standardDiagramEven 1 (by omega)).2.2
    have hchild : youngRow mu 0 = 0 := by
      unfold youngRow
      simp
    have hbad : (1 : ℕ) ≤ 0 := by
      simp [i0, hparent, hchild] at hle
    omega
  · intro hmu
    simp at hmu

/-- The standard shape `(1,1)` has the empty diagram as its only vertical
two-strip child. -/
theorem verticalTwoStripChildrenEven_standardDiagramEven_one :
    verticalTwoStripChildrenEven 1 (standardDiagramEven 1 (by omega)) =
      {oneRowDiagram 0} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hmu_eq : mu = oneRowDiagram 0 := by
      apply youngDiagram_ext
      intro i
      unfold youngRow
      simp
    exact Finset.mem_singleton.mpr hmu_eq
  · intro hmu
    have hmu_eq : mu = oneRowDiagram 0 := Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [IsVerticalTwoStripChild, IsYoungSubdiagram, standardDiagramEven,
      twoRowDiagram, oneRowDiagram, youngRow]

/-- The standard shape has no high local character weight. -/
theorem hEven_standardDiagramEven_formula
    [TwoStripDimensionBranchingAssumption] (m : ℕ) (hm : 1 ≤ m) :
    hEven m (standardDiagramEven m hm) = 0 := by
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
          change hEven 1 (standardDiagramEven 1 (by omega)) = 0
          rw [hEven]
          rw [horizontalTwoStripChildrenEven_standardDiagramEven_one]
          rw [verticalTwoStripChildrenEven_standardDiagramEven_one]
          change
            (∅ : Finset (YoungDiagram 0)).sum
                (fun mu => hEven 0 mu) +
              ({oneRowDiagram 0} : Finset (YoungDiagram 0)).sum
                (fun mu => youngDim mu - zEven 0 mu) = 0
          rw [Finset.sum_empty]
          rw [Finset.sum_singleton]
          rw [zero_add]
          change youngDim (oneRowDiagram (2 * 0)) -
            zEven 0 (oneRowDiagram (2 * 0)) = 0
          rw [youngDim_oneRowDiagram_even]
          simp [zEven]
      | succ k =>
          have hm2 : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hshape :
              standardDiagramEven (Nat.succ (Nat.succ k)) hm =
                standardDiagramEven (Nat.succ (Nat.succ k)) (by omega) := by
            exact standardDiagramEven_proof_irrel _ hm (by omega)
          rw [hshape]
          change
            hEven (Nat.succ (Nat.succ k))
              (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) = 0
          rw [hEven]
          have hh :=
            horizontalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          have hv :=
            verticalTwoStripChildrenEven_standardDiagramEven
              (Nat.succ (Nat.succ k)) hm2
          rw [hh, hv]
          let a : YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)) :=
            oneRowDiagram (2 * (Nat.succ (Nat.succ k) - 1))
          let b : YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)) :=
            standardDiagramEven (Nat.succ (Nat.succ k) - 1) (by omega)
          have hba : b ≠ a := by
            intro h
            have hrow := congrArg (fun yd => youngRow yd 1) h
            have hb1 : youngRow b 1 = 1 := by
              dsimp [b]
              exact (isStandard_standardDiagramEven
                (Nat.succ (Nat.succ k) - 1) (by omega)).2.2
            have ha1 : youngRow a 1 = 0 := by
              dsimp [a]
              rw [youngRow_oneRowDiagram]
              simp
            omega
          change
            ({a, b} : Finset
                (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                (fun mu => hEven (Nat.succ k) mu) +
              ({a} : Finset
                (YoungDiagram (2 * (Nat.succ (Nat.succ k) - 1)))).sum
                (fun mu => youngDim mu - zEven (Nat.succ k) mu) = 0
          rw [Finset.sum_insert]
          · rw [Finset.sum_singleton]
            rw [Finset.sum_singleton]
            dsimp [a, b]
            change
              hEven (Nat.succ k) (oneRowDiagram (2 * Nat.succ k)) +
                hEven (Nat.succ k)
                  (standardDiagramEven (Nat.succ k) (by omega)) +
                (youngDim (oneRowDiagram (2 * Nat.succ k)) -
                  zEven (Nat.succ k) (oneRowDiagram (2 * Nat.succ k))) = 0
            rw [hEven_oneRowDiagram]
            rw [ih (by omega : 1 ≤ Nat.succ k)]
            rw [youngDim_oneRowDiagram_even]
            rw [zEven_oneRowDiagram]
            ring
          · intro hmem
            rw [Finset.mem_singleton] at hmem
            exact hba hmem.symm

/-- The high-weight even count is nonnegative. -/
theorem hEven_nonneg [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    0 ≤ hEven m lam := by
  induction m with
  | zero =>
      simp [hEven]
  | succ m ih =>
      rw [hEven]
      apply add_nonneg
      · exact Finset.sum_nonneg (fun mu _hmu => ih mu)
      · exact Finset.sum_nonneg (fun mu _hmu =>
          sub_nonneg.mpr (zEven_le_youngDim m mu))

/-- In size two, every non-one-row diagram is the standard diagram. -/
theorem isStandard_of_not_isOneRow_size_two
    (lam : YoungDiagram (2 * 1)) (hrow : ¬ IsOneRow lam) :
    IsStandard lam := by
  have hsum : youngRow lam 0 + youngRow lam 1 = 2 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_two] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow lam 1 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h0le : youngRow lam 0 ≤ 2 := youngRow_le_size lam 0
  have h0ne : youngRow lam 0 ≠ 2 := by
    intro h0
    exact hrow h0
  have h0 : youngRow lam 0 = 1 := by omega
  have h1 : youngRow lam 1 = 1 := by omega
  exact ⟨by omega, by omega, h1⟩

/-- Base case for the upper bound on `hEven`. -/
theorem hEven_le_youngDim_m_one [TwoStripDimensionBranchingAssumption]
    (lam : YoungDiagram (2 * 1)) :
    hEven 1 lam ≤ youngDim lam := by
  by_cases hrow : IsOneRow lam
  · rw [eq_oneRowDiagram_of_isOneRow lam hrow]
    rw [hEven_oneRowDiagram]
    exact youngDim_nonneg _
  · have hstd := isStandard_of_not_isOneRow_size_two lam hrow
    rw [eq_standardDiagramEven_of_isStandard 1 (by omega) lam hstd]
    rw [hEven_standardDiagramEven_formula]
    exact youngDim_nonneg _

/-- The high-weight even count is bounded by the full Young dimension. -/
theorem hEven_le_youngDim [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (lam : YoungDiagram (2 * m)) :
    hEven m lam ≤ youngDim lam := by
  induction m with
  | zero =>
      simp [hEven]
      exact youngDim_nonneg lam
  | succ m ih =>
      cases m with
      | zero =>
          exact hEven_le_youngDim_m_one lam
      | succ m =>
          rw [hEven]
          have hH :
              (horizontalTwoStripChildrenEven (Nat.succ (Nat.succ m)) lam).sum
                  (fun mu => hEven (Nat.succ m) mu) ≤
                (horizontalTwoStripChildrenEven (Nat.succ (Nat.succ m)) lam).sum
                  (fun mu => youngDim mu) := by
            exact Finset.sum_le_sum (fun mu _hmu => ih mu)
          have hV :
              (verticalTwoStripChildrenEven (Nat.succ (Nat.succ m)) lam).sum
                  (fun mu => youngDim mu - zEven (Nat.succ m) mu) ≤
                (verticalTwoStripChildrenEven (Nat.succ (Nat.succ m)) lam).sum
                  (fun mu => youngDim mu) := by
            exact Finset.sum_le_sum (fun mu _hmu =>
              sub_le_self _ (zEven_nonneg (Nat.succ m) mu))
          have hrec :=
            youngDim_twoStrip_recurrence (Nat.succ (Nat.succ m)) (by omega) lam
          linarith

/-- Formula for `hEven` on the canonical three-row exception `(2m-2,1,1)`. -/
theorem hEven_twoRowOneOneDiagramEven_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    hEven m (twoRowOneOneDiagramEven m hm) =
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
              have hshape :
                  twoRowOneOneDiagramEven 2 hm =
                    twoRowOneOneDiagramEven 2 (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel 2 hm (by omega)
              rw [hshape]
              change
                hEven 2 (twoRowOneOneDiagramEven 2 (by omega)) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [hEven]
              rw [horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven_two]
              rw [verticalTwoStripChildrenEven_twoRowOneOneDiagramEven_two]
              let a : YoungDiagram (2 * (2 - 1)) := oneRowDiagram 2
              let b : YoungDiagram (2 * (2 - 1)) := standardDiagramEven 1 (by omega)
              have hba : b ≠ a := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 1) h
                have hb1 : youngRow b 1 = 1 := by
                  dsimp [b]
                  exact (isStandard_standardDiagramEven 1 (by omega)).2.2
                have ha1 : youngRow a 1 = 0 := by
                  dsimp [a]
                  rw [youngRow_oneRowDiagram]
                  simp
                omega
              have ha_not : a ∉ ({b} : Finset (YoungDiagram (2 * (2 - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              change
                ({b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => hEven 1 mu) +
                  ({a, b} : Finset (YoungDiagram (2 * (2 - 1)))).sum
                    (fun mu => youngDim mu - zEven 1 mu) =
                    (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b]
              change
                hEven 1 (standardDiagramEven 1 (by omega)) +
                  ((youngDim (oneRowDiagram (2 * 1)) -
                    zEven 1 (oneRowDiagram (2 * 1))) +
                    (youngDim (standardDiagramEven 1 (by omega)) -
                      zEven 1 (standardDiagramEven 1 (by omega)))) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [hEven_standardDiagramEven_formula]
              rw [youngDim_oneRowDiagram_even]
              rw [zEven_oneRowDiagram]
              rw [youngDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hshape :
                  twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) hm =
                    twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel _ hm (by omega)
              rw [hshape]
              change
                hEven (Nat.succ (Nat.succ (Nat.succ k)))
                  (twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) (by omega)) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEven]
              have hh :=
                horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              rw [hh, hv]
              let a : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowOneOneDiagramEven
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
              have hbc : b ≠ c := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 2) h
                have hb2 : youngRow b 2 = 0 := by
                  dsimp [b]
                  unfold standardDiagramEven
                  rw [youngRow_twoRowDiagram]
                  simp
                have hc2 : youngRow c 2 = 1 := by
                  dsimp [c]
                  exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hbc hmem
              have ha_not :
                  a ∉ ({b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              change
                ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => hEven (Nat.succ (Nat.succ k)) mu) +
                  ({a, b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => youngDim mu - zEven (Nat.succ (Nat.succ k)) mu) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                hEven (Nat.succ (Nat.succ k))
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  hEven (Nat.succ (Nat.succ k))
                    (twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) +
                  ((youngDim (oneRowDiagram (2 * Nat.succ (Nat.succ k))) -
                    zEven (Nat.succ (Nat.succ k))
                      (oneRowDiagram (2 * Nat.succ (Nat.succ k)))) +
                    (youngDim
                        (standardDiagramEven
                          (Nat.succ (Nat.succ k)) (by omega)) -
                      zEven (Nat.succ (Nat.succ k))
                        (standardDiagramEven
                          (Nat.succ (Nat.succ k)) (by omega)))) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEven_standardDiagramEven_formula]
              have ih211 := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ih211]
              rw [youngDim_oneRowDiagram_even]
              rw [zEven_oneRowDiagram]
              rw [youngDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- Dimension formula for the canonical three-row exception `(2m-2,1,1)`. -/
theorem youngDim_twoRowOneOneDiagramEven_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    youngDim (twoRowOneOneDiagramEven m hm) =
      (2 * (m : ℝ) - 1) * ((m : ℝ) - 1) := by
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
              have hshape :
                  twoRowOneOneDiagramEven 2 hm =
                    twoRowOneOneDiagramEven 2 (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel 2 hm (by omega)
              rw [hshape]
              change
                youngDim (twoRowOneOneDiagramEven 2 (by omega)) =
                  (2 * (2 : ℝ) - 1) * ((2 : ℝ) - 1)
              have hnat :
                  youngDimNat (twoRowOneOneDiagramEven 2 (by omega)) = 3 := by
                native_decide +revert
              norm_num [youngDim, hnat]
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              have hshape :
                  twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) hm =
                    twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ (Nat.succ k))) (by omega) := by
                exact twoRowOneOneDiagramEven_proof_irrel _ hm (by omega)
              rw [hshape]
              have hrec :=
                youngDim_twoStrip_branching_input
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
                  (twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) (by omega))
              have hh :=
                horizontalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowOneOneDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              rw [hh, hv] at hrec
              let a : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                oneRowDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1))
              let b : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                standardDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)
              let c : YoungDiagram
                  (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)) :=
                twoRowOneOneDiagramEven
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
              have hbc : b ≠ c := by
                intro h
                have hrow := congrArg (fun yd => youngRow yd 2) h
                have hb2 : youngRow b 2 = 0 := by
                  dsimp [b]
                  unfold standardDiagramEven
                  rw [youngRow_twoRowDiagram]
                  simp
                have hc2 : youngRow c 2 = 1 := by
                  dsimp [c]
                  exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k)) - 1) (by omega)).2.2
                omega
              have hb_not :
                  b ∉ ({c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hbc hmem
              have ha_not :
                  a ∉ ({b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))) := by
                intro hmem
                rw [Finset.mem_singleton] at hmem
                exact hba hmem.symm
              rw [hrec]
              change
                ({b, c} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => youngDim mu) +
                  ({a, b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => youngDim mu) =
                    (2 * ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1)
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                youngDim
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  youngDim
                    (twoRowOneOneDiagramEven
                      (Nat.succ (Nat.succ k)) (by omega)) +
                  (youngDim (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                    youngDim
                      (standardDiagramEven
                        (Nat.succ (Nat.succ k)) (by omega))) =
                    (2 * ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1)
              rw [youngDim_standardDiagramEven_formula]
              have ih211 := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ih211]
              rw [youngDim_oneRowDiagram_even]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- Row formula for `(1,1,1,1)`. -/
theorem youngRow_fourColumnDiagramFour (i : ℕ) :
    youngRow fourColumnDiagramFour i = if i < 4 then 1 else 0 := by
  unfold youngRow fourColumnDiagramFour
  by_cases hi : i < 4
  · simp [hi]
  · simp [hi]

/-- If a size-four diagram has first row `1`, it is `(1,1,1,1)`. -/
theorem eq_fourColumnDiagramFour_of_youngRow_zero_eq_one
    (lam : YoungDiagram 4) (h0 : youngRow lam 0 = 1) :
    lam = fourColumnDiagramFour := by
  have hsum : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 + youngRow lam 3 = 4 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_four] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow lam 1 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h20 : youngRow lam 2 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  have h30 : youngRow lam 3 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 3 (by norm_num)) (by norm_num)
    simpa using hle
  have h1 : youngRow lam 1 = 1 := by omega
  have h2 : youngRow lam 2 = 1 := by omega
  have h3 : youngRow lam 3 = 1 := by omega
  apply youngDiagram_ext
  intro i
  rw [youngRow_fourColumnDiagramFour]
  by_cases hi0 : i = 0
  · subst i
    simp [h0]
  · by_cases hi1 : i = 1
    · subst i
      simp [h1]
    · by_cases hi2 : i = 2
      · subst i
        simp [h2]
      · by_cases hi3 : i = 3
        · subst i
          simp [h3]
        · have hige4 : 4 ≤ i := by omega
          have hnot : ¬ i < 4 := by omega
          unfold youngRow
          simp [hnot]

/-- `(1,1)` is the vertical child of `(1,1,1,1)`. -/
theorem standardDiagramEven_verticalChild_fourColumnDiagramFour :
    IsVerticalTwoStripChild fourColumnDiagramFour
      (standardDiagramEven 1 (by omega)) := by
  constructor
  · norm_num
  constructor
  · intro i
    rw [youngRow_fourColumnDiagramFour]
    unfold standardDiagramEven
    rw [youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · by_cases hi3 : (i : ℕ) = 3
          · simp [hi3]
          · have hnot : ¬ (i : ℕ) < 4 := by omega
            simp [hi0, hi1, hnot]
  · intro i
    rw [youngRow_fourColumnDiagramFour]
    unfold standardDiagramEven
    rw [youngRow_twoRowDiagram]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · by_cases hi1 : (i : ℕ) = 1
      · simp [hi1]
      · by_cases hi2 : (i : ℕ) = 2
        · simp [hi2]
        · by_cases hi3 : (i : ℕ) = 3
          · simp [hi3]
          · have hnot : ¬ (i : ℕ) < 4 := by omega
            simp [hi0, hi1, hnot]

/-- The column shape has no horizontal two-strip child. -/
theorem horizontalTwoStripChildrenEven_fourColumnDiagramFour :
    horizontalTwoStripChildrenEven 2 fourColumnDiagramFour = ∅ := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip : IsHorizontalTwoStripChild fourColumnDiagramFour mu :=
      (Finset.mem_filter.mp hmu).2
    let i2 : Fin (2 * 2) := Fin.mk 2 (by omega)
    have hle := hstrip.2.2 i2
    have hparent : youngRow fourColumnDiagramFour 3 = 1 := by
      rw [youngRow_fourColumnDiagramFour]
      simp
    have hchild : youngRow mu 2 = 0 := by
      unfold youngRow
      simp
    have : (1 : ℕ) ≤ 0 := by
      simp [i2, hparent, hchild] at hle
    omega
  · intro hmu
    simp at hmu

/-- The column shape has exactly the standard vertical child `(1,1)`. -/
theorem verticalTwoStripChildrenEven_fourColumnDiagramFour :
    verticalTwoStripChildrenEven 2 fourColumnDiagramFour =
      {standardDiagramEven 1 (by omega)} := by
  classical
  ext mu
  constructor
  · intro hmu
    have hstrip : IsVerticalTwoStripChild fourColumnDiagramFour mu :=
      (Finset.mem_filter.mp hmu).2
    have hsum01 : youngRow mu 0 + youngRow mu 1 = 2 := by
      exact youngRow_zero_add_one_eq_size_of_tail_zero
        (by omega : 2 ≤ 2) mu (by
          intro i hi
          unfold youngRow
          simp [show ¬ i < 2 by omega])
    have hmu0_le : youngRow mu 0 ≤ 1 := by
      let i0 : Fin (2 * 2) := Fin.mk 0 (by omega)
      have hsub := hstrip.2.1 i0
      have hparent : youngRow fourColumnDiagramFour 0 = 1 := by
        rw [youngRow_fourColumnDiagramFour]
        simp
      simpa [i0, hparent] using hsub
    have hmu1_le_mu0 : youngRow mu 1 ≤ youngRow mu 0 := by
      unfold youngRow
      have hle := mu.nonincreasing
        (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
      simpa using hle
    have hmu0 : youngRow mu 0 = 1 := by omega
    have hmu1 : youngRow mu 1 = 1 := by omega
    have hstd : IsStandard mu := by
      unfold IsStandard
      constructor
      · omega
      constructor
      · omega
      · exact hmu1
    exact Finset.mem_singleton.mpr
      (eq_standardDiagramEven_of_isStandard 1 (by omega) mu hstd)
  · intro hmu
    have hmu_eq : mu = standardDiagramEven 1 (by omega) :=
      Finset.mem_singleton.mp hmu
    subst hmu_eq
    unfold verticalTwoStripChildrenEven
    simp [standardDiagramEven_verticalChild_fourColumnDiagramFour]

/-- Dimension of the size-four column shape. -/
theorem youngDim_fourColumnDiagramFour :
    youngDim fourColumnDiagramFour = 1 := by
  have hnat : youngDimNat fourColumnDiagramFour = 1 := by
    native_decide +revert
  norm_num [youngDim, hnat]

/-- The size-four column shape contributes one high-weight character. -/
theorem hEven_fourColumnDiagramFour [TwoStripDimensionBranchingAssumption] :
    hEven 2 fourColumnDiagramFour = 1 := by
  rw [hEven]
  rw [horizontalTwoStripChildrenEven_fourColumnDiagramFour]
  rw [verticalTwoStripChildrenEven_fourColumnDiagramFour]
  rw [Finset.sum_empty]
  rw [Finset.sum_singleton]
  change 0 + (youngDim (standardDiagramEven 1 (by omega)) -
    zEven 1 (standardDiagramEven 1 (by omega))) = 1
  rw [youngDim_standardDiagramEven_formula]
  rw [zEven_standardDiagramEven_formula]
  norm_num

/-- Formula for `hEven` on the canonical two-row exception `(2m-2,2)`. -/
theorem hEven_twoRowTwoDiagramEven_formula
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m) :
    hEven m (twoRowTwoDiagramEven m hm) =
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
                hEven 2 (twoRowTwoDiagramEven 2 (by omega)) =
                  (2 : ℝ) * ((2 : ℝ) - 1) / 2
              rw [hEven]
              rw [horizontalTwoStripChildrenEven_twoRowTwoDiagramEven_two]
              rw [verticalTwoStripChildrenEven_twoRowTwoDiagramEven 2 (by omega)]
              rw [Finset.sum_singleton]
              rw [Finset.sum_singleton]
              rw [hEven_oneRowDiagram]
              rw [youngDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num
          | succ k =>
              have hm3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by omega
              change
                hEven (Nat.succ (Nat.succ (Nat.succ k)))
                  (twoRowTwoDiagramEven
                    (Nat.succ (Nat.succ (Nat.succ k))) hm) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEven]
              have hh :=
                horizontalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) hm3
              have hv :=
                verticalTwoStripChildrenEven_twoRowTwoDiagramEven
                  (Nat.succ (Nat.succ (Nat.succ k))) (by omega)
              rw [hh, hv]
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
                    (fun mu => hEven (Nat.succ (Nat.succ k)) mu) +
                  ({b} : Finset
                    (YoungDiagram
                      (2 * (Nat.succ (Nat.succ (Nat.succ k)) - 1)))).sum
                    (fun mu => youngDim mu - zEven (Nat.succ (Nat.succ k)) mu) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [Finset.sum_insert ha_not]
              rw [Finset.sum_insert hb_not]
              rw [Finset.sum_singleton]
              rw [Finset.sum_singleton]
              dsimp [a, b, c]
              change
                hEven (Nat.succ (Nat.succ k))
                    (oneRowDiagram (2 * Nat.succ (Nat.succ k))) +
                  (hEven (Nat.succ (Nat.succ k))
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) +
                  hEven (Nat.succ (Nat.succ k))
                    (twoRowTwoDiagramEven (Nat.succ (Nat.succ k)) (by omega))) +
                  (youngDim
                    (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega)) -
                    zEven (Nat.succ (Nat.succ k))
                      (standardDiagramEven (Nat.succ (Nat.succ k)) (by omega))) =
                    ((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) *
                      (((Nat.succ (Nat.succ (Nat.succ k)) : ℕ) : ℝ) - 1) / 2
              rw [hEven_oneRowDiagram]
              rw [hEven_standardDiagramEven_formula]
              have ihtwo := ih (by omega : 2 ≤ Nat.succ (Nat.succ k))
              rw [ihtwo]
              rw [youngDim_standardDiagramEven_formula]
              rw [zEven_standardDiagramEven_formula]
              norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_mul]
              ring_nf

/-- Base case `m = 2` for the even certificate.  This is a finite check over
the non-one-row, nonstandard partitions of `4`: `(2,2)`, `(2,1,1)`, and
`(1,1,1,1)`. -/
theorem hEven_ge_one_fifth_youngDim_m_two
    [TwoStripDimensionBranchingAssumption]
    (lam : YoungDiagram (2 * 2))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven 2 lam := by
  have hsum : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 + youngRow lam 3 = 4 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_four] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow lam 1 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h20 : youngRow lam 2 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  have h30 : youngRow lam 3 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 3 (by norm_num)) (by norm_num)
    simpa using hle
  have h21 : youngRow lam 2 ≤ youngRow lam 1 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 1 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  have h32 : youngRow lam 3 ≤ youngRow lam 2 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 2 (by norm_num)) (j := Fin.mk 3 (by norm_num)) (by norm_num)
    simpa using hle
  have h0_ne4 : youngRow lam 0 ≠ 4 := by
    intro h0
    apply hrow
    unfold IsOneRow
    exact h0
  have h0_le4 : youngRow lam 0 ≤ 4 := by
    simpa using youngRow_le_size lam 0
  have h0_cases :
      youngRow lam 0 = 1 ∨ youngRow lam 0 = 2 ∨ youngRow lam 0 = 3 := by
    omega
  rcases h0_cases with h0 | hrest
  · rw [eq_fourColumnDiagramFour_of_youngRow_zero_eq_one lam h0]
    rw [hEven_fourColumnDiagramFour]
    rw [youngDim_fourColumnDiagramFour]
    norm_num
  rcases hrest with h0 | h0
  · have h1_cases : youngRow lam 1 = 2 ∨ youngRow lam 1 = 1 := by
      omega
    rcases h1_cases with h1 | h1
    · have hshape : IsTwoRowTwoException 2 lam := by
        unfold IsTwoRowTwoException
        constructor
        · omega
        · exact h1
      rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException 2 (by omega) lam hshape]
      rw [hEven_twoRowTwoDiagramEven_formula]
      rw [youngDim_twoRowTwoDiagramEven_formula]
      norm_num
    · have h2 : youngRow lam 2 = 1 := by omega
      have hshape : IsTwoRowOneOneException 2 lam := by
        unfold IsTwoRowOneOneException
        constructor
        · omega
        constructor
        · exact h1
        · exact h2
      rw [eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException 2 (by omega) lam hshape]
      rw [hEven_twoRowOneOneDiagramEven_formula]
      rw [youngDim_twoRowOneOneDiagramEven_formula]
      norm_num
  · have h1 : youngRow lam 1 = 1 := by omega
    exfalso
    apply hstd
    unfold IsStandard
    constructor
    · norm_num
    constructor
    · omega
    · exact h1

/-- Dimension of the size-four column shape, using actual tableau counts. -/
theorem tableauDim_fourColumnDiagramFour :
    tableauDim fourColumnDiagramFour = 1 := by
  have hrec :=
    tableauDim_twoStripChildrenEven_branching_succ 1 fourColumnDiagramFour
  rw [horizontalTwoStripChildrenEven_fourColumnDiagramFour] at hrec
  rw [verticalTwoStripChildrenEven_fourColumnDiagramFour] at hrec
  rw [hrec]
  rw [Finset.sum_empty]
  rw [Finset.sum_singleton]
  rw [tableauDim_standardDiagramEven_formula]
  norm_num

/-- The size-four column shape contributes one high-weight character in the
tableau-count recurrence. -/
theorem hEvenTableau_fourColumnDiagramFour :
    hEvenTableau 2 fourColumnDiagramFour = 1 := by
  rw [hEvenTableau]
  rw [horizontalTwoStripChildrenEven_fourColumnDiagramFour]
  rw [verticalTwoStripChildrenEven_fourColumnDiagramFour]
  rw [Finset.sum_empty]
  rw [Finset.sum_singleton]
  change 0 + (tableauDim (standardDiagramEven 1 (by omega)) -
    zEven 1 (standardDiagramEven 1 (by omega))) = 1
  rw [tableauDim_standardDiagramEven_formula]
  rw [zEven_standardDiagramEven_formula]
  norm_num

/-- Base case `m = 2` for the tableau-count even certificate. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_m_two
    (lam : YoungDiagram (2 * 2))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau 2 lam := by
  have hsum : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 + youngRow lam 3 = 4 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_four] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow lam 1 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h20 : youngRow lam 2 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  have h30 : youngRow lam 3 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 3 (by norm_num)) (by norm_num)
    simpa using hle
  have h21 : youngRow lam 2 ≤ youngRow lam 1 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 1 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  have h32 : youngRow lam 3 ≤ youngRow lam 2 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 2 (by norm_num)) (j := Fin.mk 3 (by norm_num)) (by norm_num)
    simpa using hle
  have h0_ne4 : youngRow lam 0 ≠ 4 := by
    intro h0
    apply hrow
    unfold IsOneRow
    exact h0
  have h0_le4 : youngRow lam 0 ≤ 4 := by
    simpa using youngRow_le_size lam 0
  have h0_cases :
      youngRow lam 0 = 1 ∨ youngRow lam 0 = 2 ∨ youngRow lam 0 = 3 := by
    omega
  rcases h0_cases with h0 | hrest
  · rw [eq_fourColumnDiagramFour_of_youngRow_zero_eq_one lam h0]
    rw [hEvenTableau_fourColumnDiagramFour]
    rw [tableauDim_fourColumnDiagramFour]
    norm_num
  rcases hrest with h0 | h0
  · have h1_cases : youngRow lam 1 = 2 ∨ youngRow lam 1 = 1 := by
      omega
    rcases h1_cases with h1 | h1
    · have hshape : IsTwoRowTwoException 2 lam := by
        unfold IsTwoRowTwoException
        constructor
        · omega
        · exact h1
      rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException 2 (by omega) lam hshape]
      rw [hEvenTableau_twoRowTwoDiagramEven_formula]
      rw [tableauDim_twoRowTwoDiagramEven_formula]
      norm_num
    · have h2 : youngRow lam 2 = 1 := by omega
      have hshape : IsTwoRowOneOneException 2 lam := by
        unfold IsTwoRowOneOneException
        constructor
        · omega
        constructor
        · exact h1
        · exact h2
      rw [eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException 2 (by omega) lam hshape]
      rw [hEvenTableau_twoRowOneOneDiagramEven_formula]
      rw [tableauDim_twoRowOneOneDiagramEven_formula]
      norm_num
  · have h1 : youngRow lam 1 = 1 := by omega
    exfalso
    apply hstd
    unfold IsStandard
    constructor
    · norm_num
    constructor
    · omega
    · exact h1

/-- The four exceptional-shape checks bundled for the tableau-count even
certificate. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_even_exceptional
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hex : IsEvenHExceptional m lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  rcases hex with h22 | hrest
  · exact hEvenTableau_ge_one_fifth_tableauDim_twoRowTwoException m hm lam h22
  rcases hrest with h211 | hrest
  · exact hEvenTableau_ge_one_fifth_tableauDim_twoRowOneOneException m hm lam h211
  rcases hrest with h33 | h321
  · exact hEvenTableau_ge_one_fifth_tableauDim_twoRowThreeException m hm lam h33
  · exact hEvenTableau_ge_one_fifth_tableauDim_threeRowTwoOneException m hm lam h321

/-- Finite Young-diagram induction behind Lemma 5.25, using actual tableau
counts. -/
theorem hEvenTableau_ge_one_fifth_tableauDim_of_not_oneRow_not_standard_finite_induction
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_one : m = 1
      · subst m
        exact hEvenTableau_ge_one_fifth_tableauDim_m_two lam hrow hstd
      · have hm_ge_two : 2 ≤ m := by omega
        have hM_ge_three : 3 ≤ Nat.succ m := by omega
        by_cases hbad :
            HasOneRowHorizontalChild (Nat.succ m) lam ∨
              HasOneRowVerticalChild (Nat.succ m) lam ∨
                HasStandardHorizontalChild (Nat.succ m) lam
        · exact hEvenTableau_ge_one_fifth_tableauDim_even_exceptional
            (Nat.succ m) hM_ge_three lam
            (even_bad_child_classification
              (Nat.succ m) hM_ge_three lam hrow hstd hbad)
        · exact hEvenTableau_ge_one_fifth_tableauDim_generic_step_succ
            m (by omega) lam
            (fun mu hmu_row hmu_std => ih hm_ge_two mu hmu_row hmu_std)
            (fun mu hmu hone =>
              hbad (Or.inl ⟨mu, hmu, hone⟩))
            (fun mu hmu hstd_mu =>
              hbad (Or.inr (Or.inr ⟨mu, hmu, hstd_mu⟩)))
            (fun mu hmu hone =>
              hbad (Or.inr (Or.inl ⟨mu, hmu, hone⟩)))

/-- Lemma 5.25, tableau-count version of the even certificate. -/
theorem S05_Lem5_25_tableau_even_certificate
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * tableauDim lam ≤ hEvenTableau m lam := by
  exact
    hEvenTableau_ge_one_fifth_tableauDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

/-- Exceptional case `(2m-2,2)`. -/
theorem hEven_ge_one_fifth_youngDim_twoRowTwoException
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowTwoException m lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  rw [eq_twoRowTwoDiagramEven_of_isTwoRowTwoException m (by omega) lam hshape]
  rw [hEven_twoRowTwoDiagramEven_formula m (by omega)]
  rw [youngDim_twoRowTwoDiagramEven_formula m (by omega)]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Exceptional case `(2m-2,1,1)`. -/
theorem hEven_ge_one_fifth_youngDim_twoRowOneOneException
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowOneOneException m lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  rw [eq_twoRowOneOneDiagramEven_of_isTwoRowOneOneException m (by omega) lam hshape]
  rw [hEven_twoRowOneOneDiagramEven_formula m (by omega)]
  rw [youngDim_twoRowOneOneDiagramEven_formula m (by omega)]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Recursive exceptional check for the canonical shape `(2m-3,3)`. -/
theorem hEven_ge_one_fifth_youngDim_twoRowThreeDiagramEven
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) :
    (1 / 5 : ℝ) * youngDim (twoRowThreeDiagramEven m hm) ≤
      hEven m (twoRowThreeDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_two : m = 2
      · subst m
        have hshape :
            twoRowThreeDiagramEven 3 hm =
              twoRowThreeDiagramEven 3 (by omega) := by
          exact twoRowThreeDiagramEven_proof_irrel 3 hm (by omega)
        rw [hshape]
        have hdim :
            youngDim (twoRowThreeDiagramEven 3 (by omega)) = 5 := by
          have hnat :
              youngDimNat (twoRowThreeDiagramEven 3 (by omega)) = 5 := by
            native_decide +revert
          norm_num [youngDim, hnat]
        rw [hdim]
        rw [hEven]
        rw [horizontalTwoStripChildrenEven_twoRowThreeDiagramEven_three]
        rw [verticalTwoStripChildrenEven_twoRowThreeDiagramEven 3 (by omega)]
        rw [Finset.sum_singleton]
        rw [Finset.sum_singleton]
        rw [hEven_standardDiagramEven_formula]
        rw [youngDim_twoRowTwoDiagramEven_formula]
        rw [zEven_twoRowTwoDiagramEven_formula]
        norm_num
      · have hm4 : 4 ≤ Nat.succ m := by omega
        have hmprev : 3 ≤ m := by omega
        have hshape :
            twoRowThreeDiagramEven (Nat.succ m) hm =
              twoRowThreeDiagramEven (Nat.succ m) (by omega) := by
          exact twoRowThreeDiagramEven_proof_irrel (Nat.succ m) hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (Nat.succ m - 1)) :=
          standardDiagramEven (Nat.succ m - 1) (by omega)
        let b : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowTwoDiagramEven (Nat.succ m - 1) (by omega)
        let c : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowThreeDiagramEven (Nat.succ m - 1) (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 3 := by
            dsimp [c]
            exact (isTwoRowThreeException_twoRowThreeDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 3 := by
            dsimp [c]
            exact (isTwoRowThreeException_twoRowThreeDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          omega
        have ha_not :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not :
            b ∉ ({c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh :=
          horizontalTwoStripChildrenEven_twoRowThreeDiagramEven
            (Nat.succ m) hm4
        have hv :=
          verticalTwoStripChildrenEven_twoRowThreeDiagramEven
            (Nat.succ m) (by omega)
        have hdimrec :=
          youngDim_twoStrip_recurrence
            (Nat.succ m) (by omega)
            (twoRowThreeDiagramEven (Nat.succ m) (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            youngDim (twoRowThreeDiagramEven (Nat.succ m) (by omega)) =
              youngDim a + youngDim b + youngDim c + youngDim b := by
          rw [hdimrec]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu) +
              ({b} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu) =
              youngDim a + youngDim b + youngDim c + youngDim b
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEven (Nat.succ m)
                (twoRowThreeDiagramEven (Nat.succ m) (by omega)) =
              hEven m a + hEven m b + hEven m c +
                (youngDim b - zEven m b) := by
          rw [hEven]
          rw [hh, hv]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => hEven m mu) +
              ({b} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu - zEven m mu) =
              hEven m a + hEven m b + hEven m c +
                (youngDim b - zEven m b)
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c]
        change
          (1 / 5 : ℝ) *
              (youngDim (standardDiagramEven m (by omega)) +
                youngDim (twoRowTwoDiagramEven m (by omega)) +
                youngDim (twoRowThreeDiagramEven m (by omega)) +
                youngDim (twoRowTwoDiagramEven m (by omega))) ≤
            hEven m (standardDiagramEven m (by omega)) +
              hEven m (twoRowTwoDiagramEven m (by omega)) +
              hEven m (twoRowThreeDiagramEven m (by omega)) +
              (youngDim (twoRowTwoDiagramEven m (by omega)) -
                zEven m (twoRowTwoDiagramEven m (by omega)))
        rw [hEven_standardDiagramEven_formula]
        rw [hEven_twoRowTwoDiagramEven_formula]
        rw [youngDim_standardDiagramEven_formula]
        rw [youngDim_twoRowTwoDiagramEven_formula]
        rw [zEven_twoRowTwoDiagramEven_formula]
        have ihc := ih hmprev
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hmprev
        nlinarith

/-- Exceptional case `(2m-3,3)`. -/
theorem hEven_ge_one_fifth_youngDim_twoRowThreeException
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsTwoRowThreeException m lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  rw [eq_twoRowThreeDiagramEven_of_isTwoRowThreeException m hm lam hshape]
  exact hEven_ge_one_fifth_youngDim_twoRowThreeDiagramEven m hm

/-- Recursive exceptional check for the canonical shape `(2m-3,2,1)`. -/
theorem hEven_ge_one_fifth_youngDim_threeRowTwoOneDiagramEven
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) :
    (1 / 5 : ℝ) * youngDim (threeRowTwoOneDiagramEven m hm) ≤
      hEven m (threeRowTwoOneDiagramEven m hm) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_two : m = 2
      · subst m
        have hshape :
            threeRowTwoOneDiagramEven 3 hm =
              threeRowTwoOneDiagramEven 3 (by omega) := by
          exact threeRowTwoOneDiagramEven_proof_irrel 3 hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (3 - 1)) := standardDiagramEven 2 (by omega)
        let b : YoungDiagram (2 * (3 - 1)) := twoRowTwoDiagramEven 2 (by omega)
        let c : YoungDiagram (2 * (3 - 1)) := twoRowOneOneDiagramEven 2 (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven 2 (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven 2 (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hc2 : youngRow c 2 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.2
          have ha2 : youngRow a 2 = 0 := by
            dsimp [a]
            unfold standardDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven 2 (by omega)).2.1
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven 2 (by omega)).2
          omega
        have ha_not :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (3 - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not :
            b ∉ ({c} : Finset (YoungDiagram (2 * (3 - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh := horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven_three
        have hv := verticalTwoStripChildrenEven_threeRowTwoOneDiagramEven 3 (by omega)
        have hdimrec :=
          youngDim_twoStrip_recurrence
            3 (by omega) (threeRowTwoOneDiagramEven 3 (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            youngDim (threeRowTwoOneDiagramEven 3 (by omega)) =
              (youngDim a + youngDim b + youngDim c) +
                (youngDim a + youngDim b + youngDim c) := by
          rw [hdimrec]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => youngDim mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => youngDim mu) =
              (youngDim a + youngDim b + youngDim c) +
                (youngDim a + youngDim b + youngDim c)
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEven 3 (threeRowTwoOneDiagramEven 3 (by omega)) =
              (hEven 2 a + hEven 2 b + hEven 2 c) +
                ((youngDim a - zEven 2 a) +
                  (youngDim b - zEven 2 b) +
                    (youngDim c - zEven 2 c)) := by
          rw [hEven]
          rw [hh, hv]
          change
            ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => hEven 2 mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (3 - 1)))).sum
                (fun mu => youngDim mu - zEven 2 mu) =
              (hEven 2 a + hEven 2 b + hEven 2 c) +
                ((youngDim a - zEven 2 a) +
                  (youngDim b - zEven 2 b) +
                    (youngDim c - zEven 2 c))
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not]
          rw [Finset.sum_insert hb_not]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c]
        change
          (1 / 5 : ℝ) *
              ((youngDim (standardDiagramEven 2 (by omega)) +
                  youngDim (twoRowTwoDiagramEven 2 (by omega)) +
                    youngDim (twoRowOneOneDiagramEven 2 (by omega))) +
                (youngDim (standardDiagramEven 2 (by omega)) +
                  youngDim (twoRowTwoDiagramEven 2 (by omega)) +
                    youngDim (twoRowOneOneDiagramEven 2 (by omega)))) ≤
            (hEven 2 (standardDiagramEven 2 (by omega)) +
                hEven 2 (twoRowTwoDiagramEven 2 (by omega)) +
                  hEven 2 (twoRowOneOneDiagramEven 2 (by omega))) +
              ((youngDim (standardDiagramEven 2 (by omega)) -
                  zEven 2 (standardDiagramEven 2 (by omega))) +
                (youngDim (twoRowTwoDiagramEven 2 (by omega)) -
                  zEven 2 (twoRowTwoDiagramEven 2 (by omega))) +
                  (youngDim (twoRowOneOneDiagramEven 2 (by omega)) -
                    zEven 2 (twoRowOneOneDiagramEven 2 (by omega))))
        rw [hEven_standardDiagramEven_formula]
        rw [hEven_twoRowTwoDiagramEven_formula]
        rw [hEven_twoRowOneOneDiagramEven_formula]
        have hza :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            2 (standardDiagramEven 2 (by omega))
            (not_isOneRow_standardDiagramEven 2 (by omega))
        have hzb :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            2 (twoRowTwoDiagramEven 2 (by omega))
            (not_isOneRow_twoRowTwoDiagramEven 2 (by omega))
        have hzc :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            2 (twoRowOneOneDiagramEven 2 (by omega))
            (not_isOneRow_twoRowOneOneDiagramEven 2 (by omega))
        have hda := youngDim_nonneg (standardDiagramEven 2 (by omega))
        have hdb := youngDim_nonneg (twoRowTwoDiagramEven 2 (by omega))
        have hdc := youngDim_nonneg (twoRowOneOneDiagramEven 2 (by omega))
        norm_num
        nlinarith
      · have hm4 : 4 ≤ Nat.succ m := by omega
        have hmprev : 3 ≤ m := by omega
        have hshape :
            threeRowTwoOneDiagramEven (Nat.succ m) hm =
              threeRowTwoOneDiagramEven (Nat.succ m) (by omega) := by
          exact threeRowTwoOneDiagramEven_proof_irrel (Nat.succ m) hm (by omega)
        rw [hshape]
        let a : YoungDiagram (2 * (Nat.succ m - 1)) :=
          standardDiagramEven (Nat.succ m - 1) (by omega)
        let b : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowTwoDiagramEven (Nat.succ m - 1) (by omega)
        let c : YoungDiagram (2 * (Nat.succ m - 1)) :=
          twoRowOneOneDiagramEven (Nat.succ m - 1) (by omega)
        let d : YoungDiagram (2 * (Nat.succ m - 1)) :=
          threeRowTwoOneDiagramEven (Nat.succ m - 1) (by omega)
        have hba : b ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hca : c ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hc2 : youngRow c 2 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          have ha2 : youngRow a 2 = 0 := by
            dsimp [a]
            unfold standardDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hda : d ≠ a := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hd1 : youngRow d 1 = 2 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have ha1 : youngRow a 1 = 1 := by
            dsimp [a]
            exact (isStandard_standardDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          omega
        have hcb : c ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have hb1 : youngRow b 1 = 2 := by
            dsimp [b]
            exact (isTwoRowTwoException_twoRowTwoDiagramEven
              (Nat.succ m - 1) (by omega)).2
          omega
        have hdb : d ≠ b := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 2) h
          have hd2 : youngRow d 2 = 1 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.2
          have hb2 : youngRow b 2 = 0 := by
            dsimp [b]
            unfold twoRowTwoDiagramEven
            rw [youngRow_twoRowDiagram]
            simp
          omega
        have hdc : d ≠ c := by
          intro h
          have hrow := congrArg (fun yd => youngRow yd 1) h
          have hd1 : youngRow d 1 = 2 := by
            dsimp [d]
            exact (isThreeRowTwoOneException_threeRowTwoOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          have hc1 : youngRow c 1 = 1 := by
            dsimp [c]
            exact (isTwoRowOneOneException_twoRowOneOneDiagramEven
              (Nat.succ m - 1) (by omega)).2.1
          omega
        have ha_not_h :
            a ∉ ({b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac | had
          · exact hba hab.symm
          · exact hca hac.symm
          · exact hda had.symm
        have hb_not_h :
            b ∉ ({c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hbc | hbd
          · exact hcb hbc.symm
          · exact hdb hbd.symm
        have hc_not_h :
            c ∉ ({d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hdc hmem.symm
        have ha_not_v :
            a ∉ ({b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hab | hac
          · exact hba hab.symm
          · exact hca hac.symm
        have hb_not_v :
            b ∉ ({c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))) := by
          intro hmem
          rw [Finset.mem_singleton] at hmem
          exact hcb hmem.symm
        have hh :=
          horizontalTwoStripChildrenEven_threeRowTwoOneDiagramEven
            (Nat.succ m) hm4
        have hv :=
          verticalTwoStripChildrenEven_threeRowTwoOneDiagramEven
            (Nat.succ m) (by omega)
        have hdimrec :=
          youngDim_twoStrip_recurrence
            (Nat.succ m) (by omega)
            (threeRowTwoOneDiagramEven (Nat.succ m) (by omega))
        rw [hh, hv] at hdimrec
        have hdim_explicit :
            youngDim (threeRowTwoOneDiagramEven (Nat.succ m) (by omega)) =
              (youngDim a + youngDim b + youngDim c + youngDim d) +
                (youngDim a + youngDim b + youngDim c) := by
          rw [hdimrec]
          change
            ({a, b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu) =
              (youngDim a + youngDim b + youngDim c + youngDim d) +
                (youngDim a + youngDim b + youngDim c)
          rw [Finset.sum_insert ha_not_h]
          rw [Finset.sum_insert hb_not_h]
          rw [Finset.sum_insert hc_not_h]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not_v]
          rw [Finset.sum_insert hb_not_v]
          rw [Finset.sum_singleton]
          ring
        have heven_explicit :
            hEven (Nat.succ m)
                (threeRowTwoOneDiagramEven (Nat.succ m) (by omega)) =
              (hEven m a + hEven m b + hEven m c + hEven m d) +
                ((youngDim a - zEven m a) +
                  (youngDim b - zEven m b) +
                    (youngDim c - zEven m c)) := by
          rw [hEven]
          rw [hh, hv]
          change
            ({a, b, c, d} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => hEven m mu) +
              ({a, b, c} : Finset (YoungDiagram (2 * (Nat.succ m - 1)))).sum
                (fun mu => youngDim mu - zEven m mu) =
              (hEven m a + hEven m b + hEven m c + hEven m d) +
                ((youngDim a - zEven m a) +
                  (youngDim b - zEven m b) +
                    (youngDim c - zEven m c))
          rw [Finset.sum_insert ha_not_h]
          rw [Finset.sum_insert hb_not_h]
          rw [Finset.sum_insert hc_not_h]
          rw [Finset.sum_singleton]
          rw [Finset.sum_insert ha_not_v]
          rw [Finset.sum_insert hb_not_v]
          rw [Finset.sum_singleton]
          ring
        rw [hdim_explicit, heven_explicit]
        dsimp [a, b, c, d]
        change
          (1 / 5 : ℝ) *
              ((youngDim (standardDiagramEven m (by omega)) +
                  youngDim (twoRowTwoDiagramEven m (by omega)) +
                    youngDim (twoRowOneOneDiagramEven m (by omega)) +
                      youngDim (threeRowTwoOneDiagramEven m (by omega))) +
                (youngDim (standardDiagramEven m (by omega)) +
                  youngDim (twoRowTwoDiagramEven m (by omega)) +
                    youngDim (twoRowOneOneDiagramEven m (by omega)))) ≤
            (hEven m (standardDiagramEven m (by omega)) +
                hEven m (twoRowTwoDiagramEven m (by omega)) +
                  hEven m (twoRowOneOneDiagramEven m (by omega)) +
                    hEven m (threeRowTwoOneDiagramEven m (by omega))) +
              ((youngDim (standardDiagramEven m (by omega)) -
                  zEven m (standardDiagramEven m (by omega))) +
                (youngDim (twoRowTwoDiagramEven m (by omega)) -
                  zEven m (twoRowTwoDiagramEven m (by omega))) +
                  (youngDim (twoRowOneOneDiagramEven m (by omega)) -
                    zEven m (twoRowOneOneDiagramEven m (by omega))))
        rw [hEven_standardDiagramEven_formula]
        rw [hEven_twoRowTwoDiagramEven_formula]
        rw [hEven_twoRowOneOneDiagramEven_formula]
        have ihd := ih hmprev
        have hza :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            m (standardDiagramEven m (by omega))
            (not_isOneRow_standardDiagramEven m (by omega))
        have hzb :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            m (twoRowTwoDiagramEven m (by omega))
            (not_isOneRow_twoRowTwoDiagramEven m (by omega))
        have hzc :=
          zEven_le_half_youngDim_of_not_oneRow_finite_induction
            m (twoRowOneOneDiagramEven m (by omega))
            (not_isOneRow_twoRowOneOneDiagramEven m (by omega))
        have hda_non := youngDim_nonneg (standardDiagramEven m (by omega))
        have hdb_non := youngDim_nonneg (twoRowTwoDiagramEven m (by omega))
        have hdc_non := youngDim_nonneg (twoRowOneOneDiagramEven m (by omega))
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hmprev
        nlinarith

/-- Exceptional case `(2m-3,2,1)`. -/
theorem hEven_ge_one_fifth_youngDim_threeRowTwoOneException
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hshape : IsThreeRowTwoOneException m lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  rw [eq_threeRowTwoOneDiagramEven_of_isThreeRowTwoOneException m hm lam hshape]
  exact hEven_ge_one_fifth_youngDim_threeRowTwoOneDiagramEven m hm

/-- The four exceptional-shape checks bundled as a usable case split. -/
theorem hEven_ge_one_fifth_youngDim_even_exceptional
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 3 ≤ m) (lam : YoungDiagram (2 * m))
    (hex : IsEvenHExceptional m lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  rcases hex with h22 | hrest
  · exact hEven_ge_one_fifth_youngDim_twoRowTwoException m hm lam h22
  rcases hrest with h211 | hrest
  · exact hEven_ge_one_fifth_youngDim_twoRowOneOneException m hm lam h211
  rcases hrest with h33 | h321
  · exact hEven_ge_one_fifth_youngDim_twoRowThreeException m hm lam h33
  · exact hEven_ge_one_fifth_youngDim_threeRowTwoOneException m hm lam h321

/-- Finite Young-diagram induction behind Lemma 5.25. -/
theorem hEven_ge_one_fifth_youngDim_of_not_oneRow_not_standard_finite_induction
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_one : m = 1
      · subst m
        exact hEven_ge_one_fifth_youngDim_m_two lam hrow hstd
      · have hm_ge_two : 2 ≤ m := by omega
        have hM_ge_three : 3 ≤ Nat.succ m := by omega
        by_cases hbad :
            HasOneRowHorizontalChild (Nat.succ m) lam ∨
              HasOneRowVerticalChild (Nat.succ m) lam ∨
                HasStandardHorizontalChild (Nat.succ m) lam
        · exact hEven_ge_one_fifth_youngDim_even_exceptional
            (Nat.succ m) hM_ge_three lam
            (even_bad_child_classification
              (Nat.succ m) hM_ge_three lam hrow hstd hbad)
        · exact hEven_ge_one_fifth_youngDim_generic_step
            (Nat.succ m) (by omega) lam
            (fun mu hmu_row hmu_std => ih hm_ge_two mu hmu_row hmu_std)
            (fun mu hmu hone =>
              hbad (Or.inl ⟨mu, hmu, hone⟩))
            (fun mu hmu hstd_mu =>
              hbad (Or.inr (Or.inr ⟨mu, hmu, hstd_mu⟩)))
            (fun mu hmu hone =>
              hbad (Or.inr (Or.inl ⟨mu, hmu, hone⟩)))

/-- Internal numerical `youngDim` variant of the even certificate. -/
theorem S05_Int_HEvenApp [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  exact
    hEven_ge_one_fifth_youngDim_of_not_oneRow_not_standard_finite_induction
      m hm lam hrow hstd

/-- Lemma 5.25 paper-numbered alias: even certificate. -/
theorem S05_Lem5_25_even_certificate
    [TwoStripDimensionBranchingAssumption]
    (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m))
    (hrow : ¬ IsOneRow lam) (hstd : ¬ IsStandard lam) :
    (1 / 5 : ℝ) * youngDim lam ≤ hEven m lam := by
  exact S05_Int_HEvenApp m hm lam hrow hstd

end DictatorshipTesting
