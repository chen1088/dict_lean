import AlgebraicLibrary.Young.IndexedDiagram

open AlgebraicLibrary

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.S05_Int_DegreeOneYoungBlock`
- `DictatorshipTesting.Paper.S05_Lem5_18_WeightZeroEntriesAreNeverAMajority`
- `DictatorshipTesting.Paper.S05_Lem5_19_EvenCertificate`
- `DictatorshipTesting.Paper.S05_Lem5_20_OddCertificate`
-/
/-!
Internal canonical Young diagrams used by the finite-certificate checks in
Lemmas 5.23--5.26.
-/

noncomputable section

namespace DictatorshipTesting

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

/-- The standard shape `(2m-1, 1)` as a canonical two-row diagram. -/
def standardDiagramEven (m : ℕ) (hm : 1 ≤ m) : YoungDiagram (2 * m) :=
  twoRowDiagram (2 * m) (2 * m - 1) 1 (by omega) (by omega) (by omega)

/-- The two-row exception `(2m-2, 2)` as a canonical two-row diagram. -/
def twoRowTwoDiagramEven (m : ℕ) (hm : 2 ≤ m) : YoungDiagram (2 * m) :=
  twoRowDiagram (2 * m) (2 * m - 2) 2 (by omega) (by omega) (by omega)

/-- The canonical three-row Young diagram with row lengths `(a,b,c)`. -/
def threeRowDiagram (n a b c : ℕ) (hn : 3 ≤ n)
    (habc : a + b + c = n) (hgeab : b ≤ a) (hgebc : c ≤ b) :
    YoungDiagram n where
  row := fun i =>
    if (i : ℕ) = 0 then ⟨a, by omega⟩
    else if (i : ℕ) = 1 then ⟨b, by omega⟩
    else if (i : ℕ) = 2 then ⟨c, by omega⟩
    else ⟨0, Nat.succ_pos n⟩
  nonincreasing := by
    intro i j hij
    by_cases hj0 : (j : ℕ) = 0
    · have hi0 : (i : ℕ) = 0 := by omega
      simp [hi0, hj0]
    · by_cases hj1 : (j : ℕ) = 1
      · by_cases hi0 : (i : ℕ) = 0
        · simp [hi0, hj1, hgeab]
        · have hi1 : (i : ℕ) = 1 := by omega
          simp [hi1, hj1]
      · by_cases hj2 : (j : ℕ) = 2
        · by_cases hi0 : (i : ℕ) = 0
          · have hca : c ≤ a := by omega
            simp [hi0, hj2, hca]
          · by_cases hi1 : (i : ℕ) = 1
            · simp [hi1, hj2, hgebc]
            · have hi2 : (i : ℕ) = 2 := by omega
              simp [hi2, hj2]
        · simp [hj0, hj1, hj2]
  sum_rows := by
    classical
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let i2 : Fin n := ⟨2, by omega⟩
    let tail0 : Finset (Fin n) :=
      Finset.erase (Finset.univ : Finset (Fin n)) i0
    let tail1 : Finset (Fin n) := Finset.erase tail0 i1
    let tail2 : Finset (Fin n) := Finset.erase tail1 i2
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
    have hi1_tail0 : i1 ∈ tail0 := by
      dsimp [tail0]
      exact Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ i1⟩
    have hi2_tail1 : i2 ∈ tail1 := by
      dsimp [tail1, tail0]
      exact Finset.mem_erase.mpr
        ⟨hne21, Finset.mem_erase.mpr ⟨hne20, Finset.mem_univ i2⟩⟩
    have htail2_zero :
        tail2.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else if (x : ℕ) = 2 then ⟨c, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) = 0 := by
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
      have hx2 : (x : ℕ) ≠ 2 := by
        intro h
        apply hxne2
        ext
        simp [i2, h]
      simp [hx0, hx1, hx2]
    have hsum0 :
        ((if (i0 : ℕ) = 0 then ⟨a, by omega⟩
          else if (i0 : ℕ) = 1 then ⟨b, by omega⟩
          else if (i0 : ℕ) = 2 then ⟨c, by omega⟩
          else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ) +
            tail0.sum
              (fun x : Fin n =>
                ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                  else if (x : ℕ) = 1 then ⟨b, by omega⟩
                  else if (x : ℕ) = 2 then ⟨c, by omega⟩
                  else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) =
          Finset.univ.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else if (x : ℕ) = 2 then ⟨c, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) := by
      simpa [tail0] using
        Finset.add_sum_erase
          (Finset.univ : Finset (Fin n))
          (fun x : Fin n =>
            ((if (x : ℕ) = 0 then ⟨a, by omega⟩
              else if (x : ℕ) = 1 then ⟨b, by omega⟩
              else if (x : ℕ) = 2 then ⟨c, by omega⟩
              else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ))
          (Finset.mem_univ i0)
    have hsum1 :
        ((if (i1 : ℕ) = 0 then ⟨a, by omega⟩
          else if (i1 : ℕ) = 1 then ⟨b, by omega⟩
          else if (i1 : ℕ) = 2 then ⟨c, by omega⟩
          else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ) +
            tail1.sum
              (fun x : Fin n =>
                ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                  else if (x : ℕ) = 1 then ⟨b, by omega⟩
                  else if (x : ℕ) = 2 then ⟨c, by omega⟩
                  else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) =
          tail0.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else if (x : ℕ) = 2 then ⟨c, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) := by
      simpa [tail1] using
        Finset.add_sum_erase tail0
          (fun x : Fin n =>
            ((if (x : ℕ) = 0 then ⟨a, by omega⟩
              else if (x : ℕ) = 1 then ⟨b, by omega⟩
              else if (x : ℕ) = 2 then ⟨c, by omega⟩
              else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ))
          hi1_tail0
    have hsum2 :
        ((if (i2 : ℕ) = 0 then ⟨a, by omega⟩
          else if (i2 : ℕ) = 1 then ⟨b, by omega⟩
          else if (i2 : ℕ) = 2 then ⟨c, by omega⟩
          else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ) +
            tail2.sum
              (fun x : Fin n =>
                ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                  else if (x : ℕ) = 1 then ⟨b, by omega⟩
                  else if (x : ℕ) = 2 then ⟨c, by omega⟩
                  else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) =
          tail1.sum
            (fun x : Fin n =>
              ((if (x : ℕ) = 0 then ⟨a, by omega⟩
                else if (x : ℕ) = 1 then ⟨b, by omega⟩
                else if (x : ℕ) = 2 then ⟨c, by omega⟩
                else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ)) := by
      simpa [tail2] using
        Finset.add_sum_erase tail1
          (fun x : Fin n =>
            ((if (x : ℕ) = 0 then ⟨a, by omega⟩
              else if (x : ℕ) = 1 then ⟨b, by omega⟩
              else if (x : ℕ) = 2 then ⟨c, by omega⟩
              else ⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) : ℕ))
          hi2_tail1
    rw [← hsum0, ← hsum1, ← hsum2, htail2_zero]
    simp [i0, i1, i2]
    omega

/-- The canonical exceptional shape `(2m-2,1,1)`. -/
def twoRowOneOneDiagramEven (m : ℕ) (hm : 2 ≤ m) : YoungDiagram (2 * m) :=
  threeRowDiagram (2 * m) (2 * m - 2) 1 1
    (by omega) (by omega) (by omega) (by omega)

/-- The canonical exceptional shape `(2m-3,3)`. -/
def twoRowThreeDiagramEven (m : ℕ) (hm : 3 ≤ m) : YoungDiagram (2 * m) :=
  twoRowDiagram (2 * m) (2 * m - 3) 3
    (by omega) (by omega) (by omega)

/-- The canonical exceptional shape `(2m-3,2,1)`. -/
def threeRowTwoOneDiagramEven (m : ℕ) (hm : 3 ≤ m) : YoungDiagram (2 * m) :=
  threeRowDiagram (2 * m) (2 * m - 3) 2 1
    (by omega) (by omega) (by omega) (by omega)

/-- The exceptional size-four column shape `(1,1,1,1)`. -/
def fourColumnDiagramFour : YoungDiagram 4 where
  row := fun _ => Fin.mk 1 (by norm_num)
  nonincreasing := by
    intro i j hij
    simp
  sum_rows := by
    native_decide

/-- The canonical odd exceptional shape `(2m-1,2)`. -/
def twoRowTwoDiagramOdd (m : ℕ) (hm : 2 ≤ m) : YoungDiagram (2 * m + 1) :=
  twoRowDiagram (2 * m + 1) (2 * m - 1) 2
    (by omega) (by omega) (by omega)

/-- The canonical odd exceptional shape `(2m-1,1,1)`. -/
def twoRowOneOneDiagramOdd (m : ℕ) (hm : 2 ≤ m) :
    YoungDiagram (2 * m + 1) :=
  threeRowDiagram (2 * m + 1) (2 * m - 1) 1 1
    (by omega) (by omega) (by omega) (by omega)

end DictatorshipTesting
