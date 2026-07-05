import DictatorshipTesting.Paper.Aux_TableauDimension

/-!
Paper statement: Lemma 5.16 (`lem:dimension-one-box-recurrence`)
Title in paper: One-box dimension recursion.

Status: the `youngDim` statement remains an external representation-theoretic
input for `2 <= m`, because `youngDim` is currently the hook-length dimension
proxy.  The small cases `m = 0` and `m = 1` are proved directly below.

The final section exposes an assumption-free replacement layer for
`tableauDim`, the dimension obtained by counting standard Young tableaux.  This
is the intended route toward eventually removing the `youngDim` input once the
hook-length/tableau-count equality is formalized.
-/

/-!
# Young-dimension one-box branching input for Lemma 5.16

This file isolates the dimension shadow of the ordinary one-box branching rule
used in the odd Section 5 certificate.

For a Young diagram `lambda` with `2*m+1` boxes, the Specht dimension is the
sum of the dimensions of its one-box children.  This is the standard ordinary
branching input for restricting from `S_{2m+1}` to `S_{2m}`; in this scaffold,
only the remaining `2 <= m` case is external.
-/

noncomputable section

namespace DictatorshipTesting

/-- The unique Young diagram with no boxes. -/
def emptyYoungDiagram : YoungDiagram 0 where
  row := Fin.elim0
  nonincreasing := by intro i; exact Fin.elim0 i
  sum_rows := by simp

/-- There is only one Young diagram with no boxes. -/
theorem youngDiagram_zero_subsingleton : Subsingleton (YoungDiagram 0) := by
  constructor
  intro mu nu
  cases mu
  cases nu
  congr
  funext i
  exact Fin.elim0 i

/-- The one-box branching recursion in the trivial `m = 0` case. -/
theorem youngDim_oneBox_branching_zero
    (lam : YoungDiagram (2 * 0 + 1)) :
    youngDim lam = (oneBoxChildrenOdd 0 lam).sum (fun mu => youngDim mu) := by
  have hrow : youngRow lam 0 = 1 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_one] at h
    unfold youngRow
    norm_num
    simpa using h
  have hdim_lam : youngDim lam = 1 := by
    simp [youngDim, youngDimNat, youngCells, youngHookLength, hrow]
  have hchildren : oneBoxChildrenOdd 0 lam = Finset.univ := by
    ext mu
    simp [oneBoxChildrenOdd, IsOneBoxChild, IsYoungSubdiagram, youngRow]
  have hcard : Fintype.card (YoungDiagram 0) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine Exists.intro emptyYoungDiagram ?_
    intro y
    exact @Subsingleton.elim _ youngDiagram_zero_subsingleton y emptyYoungDiagram
  rw [hdim_lam, hchildren]
  simp [youngDim, youngDimNat, youngCells, hcard]

/-- The two-box Young diagram `(2)`. -/
def rowTwoDiagram : YoungDiagram 2 where
  row := fun i => if (i : ℕ) = 0 then ⟨2, by norm_num⟩ else ⟨0, by norm_num⟩
  nonincreasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  sum_rows := by
    rw [Fin.sum_univ_two]
    simp

/-- The two-box Young diagram `(1,1)`. -/
def colTwoDiagram : YoungDiagram 2 where
  row := fun _ => ⟨1, by norm_num⟩
  nonincreasing := by
    intro i j hij
    simp
  sum_rows := by
    rw [Fin.sum_univ_two]
    simp

theorem youngRow_rowTwoDiagram (i : ℕ) :
    youngRow rowTwoDiagram i = if i = 0 then 2 else 0 := by
  by_cases hi : i < 2
  · interval_cases i <;> simp [youngRow, rowTwoDiagram]
  · have hi0 : i ≠ 0 := by omega
    simp [youngRow, hi, hi0]

theorem youngRow_colTwoDiagram (i : ℕ) :
    youngRow colTwoDiagram i = if i < 2 then 1 else 0 := by
  by_cases hi : i < 2
  · interval_cases i <;> simp [youngRow, colTwoDiagram]
  · simp [youngRow, hi]

theorem youngRow_le_size_local {n : ℕ} (lam : YoungDiagram n) (i : ℕ) :
    youngRow lam i ≤ n := by
  unfold youngRow
  split
  · exact Nat.le_of_lt_succ (lam.row _).isLt
  · exact Nat.zero_le _

/-- There are only two Young diagrams with two boxes. -/
theorem youngDiagram_two_classification (mu : YoungDiagram 2) :
    mu = rowTwoDiagram ∨ mu = colTwoDiagram := by
  have hsum : youngRow mu 0 + youngRow mu 1 = 2 := by
    have h := mu.sum_rows
    rw [Fin.sum_univ_two] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow mu 1 ≤ youngRow mu 0 := by
    unfold youngRow
    have hle := mu.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h0le : youngRow mu 0 ≤ 2 := youngRow_le_size_local mu 0
  have hcases : youngRow mu 0 = 2 ∨ youngRow mu 0 = 1 := by omega
  rcases hcases with h0 | h0
  · left
    have h1 : youngRow mu 1 = 0 := by omega
    cases mu
    unfold rowTwoDiagram youngRow at h0 h1
    congr
    funext i
    fin_cases i
    · exact Fin.ext h0
    · exact Fin.ext h1
  · right
    have h1 : youngRow mu 1 = 1 := by omega
    cases mu
    unfold colTwoDiagram youngRow at h0 h1
    congr
    funext i
    fin_cases i
    · exact Fin.ext h0
    · exact Fin.ext h1

theorem youngDim_rowTwoDiagram : youngDim rowTwoDiagram = 1 := by
  simp [youngDim, youngDimNat, youngCells, youngHookLength, youngRow_rowTwoDiagram]
  native_decide

theorem youngDim_colTwoDiagram : youngDim colTwoDiagram = 1 := by
  simp [youngDim, youngDimNat, youngCells, youngHookLength, youngRow_colTwoDiagram]
  native_decide

theorem oneBoxChildrenOdd_oneRowThree
    (lam : YoungDiagram (2 * 1 + 1))
    (hrow_all : ∀ i : ℕ, youngRow lam i = if i = 0 then 3 else 0) :
    oneBoxChildrenOdd 1 lam = {rowTwoDiagram} := by
  ext mu
  constructor
  · intro hmu
    have hstrip : IsOneBoxChild lam mu := by
      simpa [oneBoxChildrenOdd] using hmu
    rcases youngDiagram_two_classification mu with rfl | rfl
    · simp
    · exfalso
      have hsub := hstrip.2 (Fin.mk 1 (by norm_num))
      rw [youngRow_colTwoDiagram, hrow_all] at hsub
      norm_num at hsub
  · intro hmu
    have hmu' : mu = rowTwoDiagram := by simpa using hmu
    subst mu
    simp [oneBoxChildrenOdd, IsOneBoxChild, IsYoungSubdiagram,
      youngRow_rowTwoDiagram, hrow_all]
    intro i
    fin_cases i <;> norm_num

theorem oneBoxChildrenOdd_standardThree
    (lam : YoungDiagram (2 * 1 + 1))
    (hrow_all : ∀ i : ℕ,
      youngRow lam i = if i = 0 then 2 else if i = 1 then 1 else 0) :
    oneBoxChildrenOdd 1 lam = {rowTwoDiagram, colTwoDiagram} := by
  ext mu
  constructor
  · intro hmu
    rcases youngDiagram_two_classification mu with rfl | rfl <;> simp
  · intro hmu
    have hcases : mu = rowTwoDiagram ∨ mu = colTwoDiagram := by simpa using hmu
    rcases hcases with rfl | rfl
    · simp [oneBoxChildrenOdd, IsOneBoxChild, IsYoungSubdiagram,
        youngRow_rowTwoDiagram, hrow_all]
      intro i
      fin_cases i <;> norm_num
    · simp [oneBoxChildrenOdd, IsOneBoxChild, IsYoungSubdiagram,
        youngRow_colTwoDiagram, hrow_all]
      intro i
      fin_cases i <;> norm_num

theorem oneBoxChildrenOdd_colThree
    (lam : YoungDiagram (2 * 1 + 1))
    (hrow_all : ∀ i : ℕ, youngRow lam i = if i < 3 then 1 else 0) :
    oneBoxChildrenOdd 1 lam = {colTwoDiagram} := by
  ext mu
  constructor
  · intro hmu
    have hstrip : IsOneBoxChild lam mu := by
      simpa [oneBoxChildrenOdd] using hmu
    rcases youngDiagram_two_classification mu with rfl | rfl
    · exfalso
      have hsub := hstrip.2 (Fin.mk 0 (by norm_num))
      rw [youngRow_rowTwoDiagram, hrow_all] at hsub
      norm_num at hsub
    · simp
  · intro hmu
    have hmu' : mu = colTwoDiagram := by simpa using hmu
    subst mu
    simp [oneBoxChildrenOdd, IsOneBoxChild, IsYoungSubdiagram,
      youngRow_colTwoDiagram, hrow_all]
    intro i
    fin_cases i <;> norm_num

theorem youngDiagram_three_row_classification (lam : YoungDiagram 3) :
    (youngRow lam 0 = 3 ∧ youngRow lam 1 = 0 ∧ youngRow lam 2 = 0) ∨
    (youngRow lam 0 = 2 ∧ youngRow lam 1 = 1 ∧ youngRow lam 2 = 0) ∨
    (youngRow lam 0 = 1 ∧ youngRow lam 1 = 1 ∧ youngRow lam 2 = 1) := by
  have hsum : youngRow lam 0 + youngRow lam 1 + youngRow lam 2 = 3 := by
    have h := lam.sum_rows
    rw [Fin.sum_univ_three] at h
    unfold youngRow
    norm_num
    simpa using h
  have h10 : youngRow lam 1 ≤ youngRow lam 0 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 0 (by norm_num)) (j := Fin.mk 1 (by norm_num)) (by norm_num)
    simpa using hle
  have h21 : youngRow lam 2 ≤ youngRow lam 1 := by
    unfold youngRow
    have hle := lam.nonincreasing
      (i := Fin.mk 1 (by norm_num)) (j := Fin.mk 2 (by norm_num)) (by norm_num)
    simpa using hle
  omega

theorem youngDim_three_row
    (lam : YoungDiagram 3)
    (h0 : youngRow lam 0 = 3) (h1 : youngRow lam 1 = 0) (h2 : youngRow lam 2 = 0) :
    youngDim lam = 1 := by
  have hrow_all : ∀ i : ℕ, youngRow lam i = if i = 0 then 3 else 0 := by
    intro i
    by_cases hi0 : i = 0
    · simp [hi0, h0]
    · by_cases hi : i < 3
      · interval_cases i <;> simp [h0, h1, h2, hi0]
      · simp [youngRow, hi, hi0]
  have hnat : youngDimNat lam = 1 := by
    unfold youngDimNat youngCells youngHookLength
    simp [hrow_all]
    native_decide
  norm_num [youngDim, hnat]

theorem youngDim_three_standard
    (lam : YoungDiagram 3)
    (h0 : youngRow lam 0 = 2) (h1 : youngRow lam 1 = 1) (h2 : youngRow lam 2 = 0) :
    youngDim lam = 2 := by
  have hrow_all : ∀ i : ℕ,
      youngRow lam i = if i = 0 then 2 else if i = 1 then 1 else 0 := by
    intro i
    by_cases hi0 : i = 0
    · simp [hi0, h0]
    · by_cases hi1 : i = 1
      · simp [hi1, h1]
      · by_cases hi : i < 3
        · interval_cases i <;> simp [h0, h1, h2, hi0, hi1]
        · simp [youngRow, hi, hi0, hi1]
  have hnat : youngDimNat lam = 2 := by
    unfold youngDimNat youngCells youngHookLength
    simp [hrow_all]
    native_decide
  norm_num [youngDim, hnat]

theorem youngDim_three_col
    (lam : YoungDiagram 3)
    (h0 : youngRow lam 0 = 1) (h1 : youngRow lam 1 = 1) (h2 : youngRow lam 2 = 1) :
    youngDim lam = 1 := by
  have hrow_all : ∀ i : ℕ, youngRow lam i = if i < 3 then 1 else 0 := by
    intro i
    by_cases hi : i < 3
    · interval_cases i <;> simp [h0, h1, h2]
    · simp [youngRow, hi]
  have hnat : youngDimNat lam = 1 := by
    unfold youngDimNat youngCells youngHookLength
    simp [hrow_all]
    native_decide
  norm_num [youngDim, hnat]

/-- The one-box branching recursion for diagrams with three boxes. -/
theorem youngDim_oneBox_branching_one
    (lam : YoungDiagram (2 * 1 + 1)) :
    youngDim lam = (oneBoxChildrenOdd 1 lam).sum (fun mu => youngDim mu) := by
  have hcases := youngDiagram_three_row_classification lam
  rcases hcases with hrow | hrow | hrow
  · rcases hrow with ⟨h0, h1, h2⟩
    have hrow_all : ∀ i : ℕ, youngRow lam i = if i = 0 then 3 else 0 := by
      intro i
      by_cases hi0 : i = 0
      · simp [hi0, h0]
      · by_cases hi : i < 3
        · interval_cases i <;> simp [h0, h1, h2, hi0]
        · simp [youngRow, hi, hi0]
    rw [youngDim_three_row lam h0 h1 h2]
    rw [oneBoxChildrenOdd_oneRowThree lam hrow_all]
    simp [youngDim_rowTwoDiagram]
  · rcases hrow with ⟨h0, h1, h2⟩
    have hrow_all : ∀ i : ℕ,
        youngRow lam i = if i = 0 then 2 else if i = 1 then 1 else 0 := by
      intro i
      by_cases hi0 : i = 0
      · simp [hi0, h0]
      · by_cases hi1 : i = 1
        · simp [hi1, h1]
        · by_cases hi : i < 3
          · interval_cases i <;> simp [h0, h1, h2, hi0, hi1]
          · simp [youngRow, hi, hi0, hi1]
    rw [youngDim_three_standard lam h0 h1 h2]
    rw [oneBoxChildrenOdd_standardThree lam hrow_all]
    have hne : rowTwoDiagram ≠ colTwoDiagram := by
      intro h
      have hrow := congrArg (fun yd => youngRow yd 0) h
      rw [youngRow_rowTwoDiagram, youngRow_colTwoDiagram] at hrow
      norm_num at hrow
    simp [youngDim_rowTwoDiagram, youngDim_colTwoDiagram, hne]
    norm_num
  · rcases hrow with ⟨h0, h1, h2⟩
    have hrow_all : ∀ i : ℕ, youngRow lam i = if i < 3 then 1 else 0 := by
      intro i
      by_cases hi : i < 3
      · interval_cases i <;> simp [h0, h1, h2]
      · simp [youngRow, hi]
    rw [youngDim_three_col lam h0 h1 h2]
    rw [oneBoxChildrenOdd_colThree lam hrow_all]
    simp [youngDim_colTwoDiagram]

/-- Explicit assumption class for the dimension shadow of the ordinary one-box
branching rule in the remaining `2 <= m` range. -/
class OneBoxDimensionBranchingPositiveAssumption : Prop where
  branch : ∀ (m : ℕ), 2 ≤ m → ∀ lam : YoungDiagram (2 * m + 1),
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu)

/-- External ordinary Specht branching input.

Reference: the ordinary branching rule for Specht modules, e.g. Sagan,
*The Symmetric Group*, Section 2.8, or James--Kerber, *The Representation
Theory of the Symmetric Group*. The rule says that restricting `S^lambda` from
`S_N` to `S_{N-1}` decomposes over all removable-corner deletions. Taking
dimensions gives this one-box recursion. -/
axiom oneBoxDimensionBranchingPositiveAssumption_from_specht_branching :
  OneBoxDimensionBranchingPositiveAssumption

attribute [instance] oneBoxDimensionBranchingPositiveAssumption_from_specht_branching

/-- Dimension shadow of the ordinary one-box branching rule in the remaining
`2 <= m` range, available from the explicit assumption class. -/
theorem youngDim_oneBox_branching_positive_input
    [OneBoxDimensionBranchingPositiveAssumption] (m : ℕ) (hm : 2 ≤ m)
    (lam : YoungDiagram (2 * m + 1)) :
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu) := by
  exact OneBoxDimensionBranchingPositiveAssumption.branch m hm lam

/-- Dimension shadow of the ordinary one-box branching rule. -/
theorem youngDim_oneBox_branching_input
    [OneBoxDimensionBranchingPositiveAssumption] (m : ℕ)
    (lam : YoungDiagram (2 * m + 1)) :
    youngDim lam = (oneBoxChildrenOdd m lam).sum (fun mu => youngDim mu) := by
  by_cases hm0 : m = 0
  · subst m
    exact youngDim_oneBox_branching_zero lam
  · by_cases hm1 : m = 1
    · subst m
      exact youngDim_oneBox_branching_one lam
    · have hm : 2 ≤ m := by omega
      exact youngDim_oneBox_branching_positive_input m hm lam

/-!
## Tableau-count replacement layer

The following wrappers are assumption-free: they use `tableauDim`, defined as the
cardinality of standard Young tableaux, rather than the hook-length proxy
`youngDim`.
-/

theorem S05_Lem5_16_tableauDim_fixed_oneBoxChild
    {n : Nat} {lam : YoungDiagram (n + 1)} {mu : YoungDiagram n}
    (h : IsOneBoxChild lam mu) {r : Nat}
    (hr :
      youngRow lam r = youngRow mu r + 1 ∧
      forall t : Nat, t ≠ r -> youngRow lam t = youngRow mu t) :
    ((Fintype.card
      {T : StandardYoungTableau lam //
        TableauMaxAt T (deletedCornerCellOfOneBoxChildRow h hr)} : Nat) : ℝ)
      =
    tableauDim mu := by
  exact tableauDim_fixed_oneBoxChild h hr

theorem S05_Lem5_16_tableauDim_oneBox_branching
    {n : Nat} (lam : YoungDiagram (n + 1)) :
    tableauDim lam =
      (oneBoxChildrenSized lam).sum (fun mu => tableauDim mu) := by
  exact tableauDim_oneBox_branching_sized lam

theorem S05_Lem5_16_tableauDim_oneBoxChildrenOdd_branching
    (m : Nat) (lam : YoungDiagram (2 * m + 1)) :
    tableauDim lam =
      (oneBoxChildrenOdd m lam).sum (fun mu => tableauDim mu) := by
  exact tableauDim_oneBoxChildrenOdd_branching m lam

end DictatorshipTesting
