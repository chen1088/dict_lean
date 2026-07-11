import DictatorshipTesting.Paper.S05_Int_ConcreteYoungMatrixCoefficientBlocks
import DictatorshipTesting.Paper.S05_Lem5_01_AdjacentTranspositionsInYoungsBasis
import DictatorshipTesting.Paper.Defs.S05_Def5_26_CertificateSpecialDiagrams
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort

/-
Direct reverse imports:
- `DictatorshipTesting.Paper.AppA_LemA_03_DegreeOneYoungBlockIdentification`
-/

/-!
# The concrete degree-one Young blocks

This internal file identifies the coefficient space of the permutation
coordinate representation with the concrete one-row and standard Young
matrix-coefficient blocks.  It supplies the faithful subspace equality used by
Appendix A.3.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- The permutation-coordinate action on real functions on a finite set. -/
def permutationCoordinateRho {α : Type*} [Fintype α]
    (pi : Perm α) (v : α -> Real) : α -> Real :=
  fun j => v (pi.symm j)

/-- The permutation-coordinate action packaged as a real representation. -/
def permutationCoordinateRepresentation (α : Type*) [Fintype α] :
    GroupRepresentationActionData (Perm α) (α -> Real) where
  rho := permutationCoordinateRho
  map_add := by
    intro pi v w
    funext j
    rfl
  map_smul := by
    intro pi c v
    funext j
    rfl
  map_mul := by
    intro pi sigma v
    funext j
    change v ((pi * sigma)⁻¹ j) = v (sigma⁻¹ (pi⁻¹ j))
    rw [mul_inv_rev]
    rfl
  map_one := by
    intro v
    funext j
    change v ((1 : Perm α)⁻¹ j) = v j
    simp

/-- The standard coordinate vector at `i`. -/
def permutationCoordinateBasisVec {α : Type*} [DecidableEq α]
    (i : α) : α -> Real :=
  fun j => if j = i then 1 else 0

/-- The Euclidean inner product on permutation coordinates. -/
def permutationCoordinateInner {α : Type*} [Fintype α]
    (v w : α -> Real) : Real :=
  ∑ i : α, v i * w i

/-- Sum all coordinates of a finite real vector. -/
def permutationCoordinateSumLinearMap (n : Nat) :
    (Fin n → Real) →ₗ[Real] Real where
  toFun v := ∑ i : Fin n, v i
  map_add' := by
    intro v w
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    simp [Finset.mul_sum]

/-- The sum-zero subspace of the permutation-coordinate representation. -/
def permutationCoordinateSumZero (n : Nat) :
    Submodule Real (Fin n → Real) :=
  LinearMap.ker (permutationCoordinateSumLinearMap n)

/-- Matrix coefficient of the coordinate permutation representation. -/
def permutationCoordinateCoefficient {α : Type*}
    [Fintype α] [DecidableEq α] (i j : α) : Perm α -> Real :=
  fun pi =>
    permutationCoordinateInner (permutationCoordinateBasisVec j)
      (permutationCoordinateRho pi (permutationCoordinateBasisVec i))

/-- A one-coset indicator is exactly a matrix coefficient of the permutation
coordinate representation. -/
theorem permutationCoordinateCoefficient_eq_oneCosetReal
    {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    permutationCoordinateCoefficient i j = oneCosetReal i j := by
  funext pi
  classical
  unfold permutationCoordinateCoefficient permutationCoordinateInner
  rw [Fintype.sum_eq_single j]
  · by_cases h : pi i = j
    · have hs : pi.symm j = i := by
        apply pi.injective
        simp [h]
      simp [permutationCoordinateBasisVec, permutationCoordinateRho,
        oneCosetReal, h, hs]
    · have hs : pi.symm j ≠ i := by
        intro hs
        apply h
        rw [← hs]
        simp
      simp [permutationCoordinateBasisVec, permutationCoordinateRho,
        oneCosetReal, h, hs]
  · intro x hx
    simp [permutationCoordinateBasisVec, hx]

/-- Coefficient space of the concrete permutation-coordinate representation. -/
def permutationCoordinateCoefficientSpace (α : Type*)
    [Fintype α] [DecidableEq α] : Submodule Real (Perm α -> Real) :=
  Submodule.span Real
    (Set.range fun ij : α × α =>
      permutationCoordinateCoefficient ij.1 ij.2)

/-- The repository's `U1` is exactly the coefficient space of the concrete
permutation-coordinate representation. -/
theorem U1_eq_permutationCoordinateCoefficientSpace
    (α : Type*) [Fintype α] [DecidableEq α] :
    U1 α = permutationCoordinateCoefficientSpace α := by
  unfold U1 permutationCoordinateCoefficientSpace
  congr 1
  ext F
  constructor
  · rintro ⟨ij, rfl⟩
    exact ⟨ij, by simpa using
      permutationCoordinateCoefficient_eq_oneCosetReal ij.1 ij.2⟩
  · rintro ⟨ij, rfl⟩
    exact ⟨ij, by simpa using
      (permutationCoordinateCoefficient_eq_oneCosetReal ij.1 ij.2).symm⟩

/-! ## The standard shape and its tableaux -/

/-- In a standard shape of size `n+1`, the first row has length `n`. -/
theorem youngRow_zero_of_isStandard {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    youngRow lam 0 = n := by
  exact hstd.2.1

/-- In a standard shape, the second row has length one. -/
theorem youngRow_one_of_isStandard {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    youngRow lam 1 = 1 := by
  exact hstd.2.2

/-- In a standard shape, every row after the second is empty. -/
theorem youngRow_eq_zero_of_isStandard_of_two_le {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    {r : Nat} (hr : 2 ≤ r) :
    youngRow lam r = 0 := by
  classical
  by_cases hrn : r < n + 1
  · have h0n : 0 < n + 1 := by omega
    have h1n : 1 < n + 1 := by omega
    let i0 : Fin (n + 1) := ⟨0, h0n⟩
    let i1 : Fin (n + 1) := ⟨1, h1n⟩
    let ir : Fin (n + 1) := ⟨r, hrn⟩
    let tail0 := (Finset.univ : Finset (Fin (n + 1))).erase i0
    let tail1 := tail0.erase i1
    have hi1 : i1 ∈ tail0 := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i1⟩
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    have hir : ir ∈ tail1 := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_univ ir⟩⟩
      · intro h
        have := congrArg Fin.val h
        simp [ir, i1] at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp [ir, i0] at this
        omega
    have hsum0 :
        (lam.row i0 : Nat) + tail0.sum (fun i => (lam.row i : Nat)) = n + 1 := by
      simpa [tail0, add_comm] using
        (Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
          (fun i => (lam.row i : Nat)) (Finset.mem_univ i0)).trans lam.sum_rows
    have hsum1 :
        (lam.row i1 : Nat) + tail1.sum (fun i => (lam.row i : Nat)) =
          tail0.sum (fun i => (lam.row i : Nat)) := by
      simpa [tail1, add_comm] using
        Finset.sum_erase_add tail0 (fun i => (lam.row i : Nat)) hi1
    have hrow0 : (lam.row i0 : Nat) = n := by
      simpa [youngRow, i0, h0n] using youngRow_zero_of_isStandard hstd
    have hrow1 : (lam.row i1 : Nat) = 1 := by
      simpa [youngRow, i1, h1n] using youngRow_one_of_isStandard hstd
    have htail : tail1.sum (fun i => (lam.row i : Nat)) = 0 := by
      omega
    have hir_le : (lam.row ir : Nat) ≤
        tail1.sum (fun i => (lam.row i : Nat)) := by
      exact Finset.single_le_sum
        (fun i _ => Nat.zero_le (lam.row i : Nat)) hir
    have hz : (lam.row ir : Nat) = 0 := by omega
    simpa [youngRow, hrn, ir] using hz
  · simp [youngRow, hrn]

/-- The unique box in the second row of a standard shape. -/
def standardLowerCell {n : Nat} {lam : YoungDiagram (n + 1)}
    (hstd : IsStandard lam) : YoungCell lam :=
  youngCellOfNat lam 1 0 (by rw [youngRow_one_of_isStandard hstd]; omega)

/-- The box in column `c` of the first row of a standard shape. -/
def standardTopCell {n : Nat} {lam : YoungDiagram (n + 1)}
    (hstd : IsStandard lam) (c : Fin n) : YoungCell lam :=
  youngCellOfNat lam 0 c (by
    rw [youngRow_zero_of_isStandard hstd]
    exact c.isLt)

@[simp] theorem standardLowerCell_row {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    YoungCell.row (standardLowerCell hstd) = 1 := by
  simp [standardLowerCell, youngCellOfNat_row]

@[simp] theorem standardLowerCell_col {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    YoungCell.col (standardLowerCell hstd) = 0 := by
  simp [standardLowerCell, youngCellOfNat_col]

@[simp] theorem standardTopCell_row {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (c : Fin n) :
    YoungCell.row (standardTopCell hstd c) = 0 := by
  simp [standardTopCell, youngCellOfNat_row]

@[simp] theorem standardTopCell_col {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (c : Fin n) :
    YoungCell.col (standardTopCell hstd c) = c := by
  simp [standardTopCell, youngCellOfNat_col]

theorem standardLowerCell_ne_standardTopCell {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (c : Fin n) :
    standardLowerCell hstd ≠ standardTopCell hstd c := by
  intro h
  have := congrArg YoungCell.row h
  simp at this

/-- Every box of a standard shape is either its lower box or a unique top-row
box. -/
theorem standardShape_cell_cases {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (u : YoungCell lam) :
    u = standardLowerCell hstd ∨
      ∃! c : Fin n, u = standardTopCell hstd c := by
  have hbox := YoungCell.isYoungBox u
  change YoungCell.col u < youngRow lam (YoungCell.row u) at hbox
  by_cases hrow0 : YoungCell.row u = 0
  · right
    have hcol_lt : YoungCell.col u < n := by
      simpa [IsYoungBox, hrow0, youngRow_zero_of_isStandard hstd] using hbox
    let c : Fin n := ⟨YoungCell.col u, hcol_lt⟩
    refine ⟨c, ?_, ?_⟩
    · apply YoungCell.ext_row_col
      · simp [hrow0]
      · simp [c]
    · intro d hd
      apply Fin.ext
      have := congrArg YoungCell.col hd
      simpa [c] using this.symm
  · have hrow1 : YoungCell.row u = 1 := by
      by_contra hne
      have htwo : 2 ≤ YoungCell.row u := by omega
      have hz := youngRow_eq_zero_of_isStandard_of_two_le hstd htwo
      rw [hz] at hbox
      omega
    left
    apply YoungCell.ext_row_col
    · simp [hrow1]
    · have hcol : YoungCell.col u = 0 := by
        have : YoungCell.col u < 1 := by
          simpa [IsYoungBox, hrow1, youngRow_one_of_isStandard hstd] using hbox
        omega
      simp [hcol]

/-- The entry in the unique lower box of a standard-shape tableau. -/
def standardLowerEntry {n : Nat} {lam : YoungDiagram (n + 1)}
    (hstd : IsStandard lam) (T : StandardYoungTableau lam) : Fin (n + 1) :=
  T.entry (standardLowerCell hstd)

/-- The lower entry of a standard-shape tableau is nonzero. -/
theorem standardLowerEntry_ne_zero {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) :
    standardLowerEntry hstd T ≠ 0 := by
  have hn : 0 < n := by
    have := hstd.1
    omega
  let c0 : Fin n := ⟨0, hn⟩
  have hlt : T.entry (standardTopCell hstd c0) <
      T.entry (standardLowerCell hstd) := by
    apply T.col_strict
    · simp [c0]
    · simp
  intro hzero
  change T.entry (standardLowerCell hstd) = 0 at hzero
  rw [hzero] at hlt
  exact Fin.not_lt_zero _ hlt

/-- The first-row entries are the increasing enumeration of all entries except
the lower-row entry. -/
theorem standardTopCell_entry_eq_succAbove {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (c : Fin n) :
    T.entry (standardTopCell hstd c) =
      (standardLowerEntry hstd T).succAbove c := by
  classical
  let p := standardLowerEntry hstd T
  let f : Fin n → Fin (n + 1) := fun d => T.entry (standardTopCell hstd d)
  have hfmem : ∀ d, f d ∈ ({p}ᶜ : Finset (Fin (n + 1))) := by
    intro d
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro h
    apply standardLowerCell_ne_standardTopCell hstd d
    exact (T.bijective.1 (by simpa [f, p, standardLowerEntry] using h)).symm
  have hfmono : StrictMono f := by
    intro a b hab
    apply T.row_strict
    · simp
    · simpa [f] using hab
  have henum := Finset.orderEmbOfFin_unique
    (s := ({p}ᶜ : Finset (Fin (n + 1)))) (k := n)
    (by simp [Finset.card_compl]) hfmem hfmono
  have hcanonical :
      ({p}ᶜ : Finset (Fin (n + 1))).orderEmbOfFin
          (by simp [Finset.card_compl]) = Fin.succAboveOrderEmb p := by
    exact Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb p
  have hc := congrFun henum c
  rw [hcanonical] at hc
  exact hc

/-- A standard-shape tableau is determined by its lower-row entry. -/
theorem standardYoungTableau_eq_of_lowerEntry_eq {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    {T S : StandardYoungTableau lam}
    (h : standardLowerEntry hstd T = standardLowerEntry hstd S) :
    T = S := by
  apply standardYoungTableau_ext_entry
  intro u
  rcases standardShape_cell_cases hstd u with hu | ⟨c, hc, _⟩
  · subst u
    exact h
  · subst u
    rw [standardTopCell_entry_eq_succAbove hstd T c,
      standardTopCell_entry_eq_succAbove hstd S c, h]

/-- Parametrize the cells of a standard shape by its top-row columns together
with the single lower cell. -/
def standardShapeCellMap {n : Nat} {lam : YoungDiagram (n + 1)}
    (hstd : IsStandard lam) : Sum (Fin n) Unit → YoungCell lam
  | Sum.inl c => standardTopCell hstd c
  | Sum.inr _ => standardLowerCell hstd

theorem standardShapeCellMap_bijective {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    Function.Bijective (standardShapeCellMap hstd) := by
  constructor
  · intro x y hxy
    cases x with
    | inl c =>
        cases y with
        | inl d =>
            have hcd : c = d := by
              apply Fin.ext
              have := congrArg YoungCell.col hxy
              simpa [standardShapeCellMap] using this
            subst d
            rfl
        | inr u =>
            exfalso
            exact standardLowerCell_ne_standardTopCell hstd c hxy.symm
    | inr u =>
        cases y with
        | inl d =>
            exfalso
            exact standardLowerCell_ne_standardTopCell hstd d hxy
        | inr v => simp
  · intro u
    rcases standardShape_cell_cases hstd u with hu | ⟨c, hc, _⟩
    · exact ⟨Sum.inr (), by simpa [standardShapeCellMap] using hu.symm⟩
    · exact ⟨Sum.inl c, by simpa [standardShapeCellMap] using hc.symm⟩

/-- The cell equivalence for a standard shape. -/
noncomputable def standardShapeCellEquiv {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    Sum (Fin n) Unit ≃ YoungCell lam :=
  Equiv.ofBijective (standardShapeCellMap hstd)
    (standardShapeCellMap_bijective hstd)

@[simp] theorem standardShapeCellEquiv_inl {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (c : Fin n) :
    standardShapeCellEquiv hstd (Sum.inl c) = standardTopCell hstd c := by
  rfl

@[simp] theorem standardShapeCellEquiv_inr {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (u : Unit) :
    standardShapeCellEquiv hstd (Sum.inr u) = standardLowerCell hstd := by
  rfl

@[simp] theorem standardShapeCellEquiv_symm_top {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (c : Fin n) :
    (standardShapeCellEquiv hstd).symm (standardTopCell hstd c) =
      Sum.inl c := by
  apply (standardShapeCellEquiv hstd).injective
  simp

@[simp] theorem standardShapeCellEquiv_symm_lower {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    (standardShapeCellEquiv hstd).symm (standardLowerCell hstd) =
      Sum.inr () := by
  apply (standardShapeCellEquiv hstd).injective
  simp

/-- Enumerate all labels except `p` along the top row and put `p` in the
lower box. -/
def standardShapeLabelMap {n : Nat} (p : Fin (n + 1)) :
    Sum (Fin n) Unit → Fin (n + 1)
  | Sum.inl c => p.succAbove c
  | Sum.inr _ => p

theorem standardShapeLabelMap_bijective {n : Nat} (p : Fin (n + 1)) :
    Function.Bijective (standardShapeLabelMap p) := by
  constructor
  · intro x y hxy
    cases x with
    | inl c =>
        cases y with
        | inl d =>
            exact congrArg Sum.inl (Fin.succAbove_right_injective hxy)
        | inr u =>
            exfalso
            have hxy' : p.succAbove c = p := by
              simpa only [standardShapeLabelMap] using hxy
            exact p.succAbove_ne c hxy'
    | inr u =>
        cases y with
        | inl d =>
            exfalso
            exact p.succAbove_ne d (by
              simpa [standardShapeLabelMap] using hxy.symm)
        | inr v => simp
  · intro y
    by_cases hy : y = p
    · exact ⟨Sum.inr (), by simp [standardShapeLabelMap, hy]⟩
    · rcases Fin.exists_succAbove_eq hy with ⟨c, hc⟩
      exact ⟨Sum.inl c, by simpa [standardShapeLabelMap] using hc⟩

/-- The canonical standard tableau with lower-row entry `p`. -/
noncomputable def standardTableauWithLowerEntry {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (p : Fin (n + 1)) (hp : p ≠ 0) : StandardYoungTableau lam where
  entry := standardShapeLabelMap p ∘ (standardShapeCellEquiv hstd).symm
  bijective := (standardShapeLabelMap_bijective p).comp
    (standardShapeCellEquiv hstd).symm.bijective
  row_strict := by
    intro u v hrow hcol
    rcases standardShape_cell_cases hstd u with hu | ⟨c, hc, _⟩
    · subst u
      rcases standardShape_cell_cases hstd v with hv | ⟨d, hd, _⟩
      · subst v
        simp at hcol
      · subst v
        simp at hrow
    · subst u
      rcases standardShape_cell_cases hstd v with hv | ⟨d, hd, _⟩
      · subst v
        simp at hrow
      · subst v
        have hcd : c < d := by simpa using hcol
        simp only [Function.comp_apply, standardShapeCellEquiv_symm_top,
          standardShapeLabelMap]
        exact Fin.strictMono_succAbove p hcd
  col_strict := by
    intro u v hcol hrow
    rcases standardShape_cell_cases hstd u with hu | ⟨c, hc, _⟩
    · subst u
      rcases standardShape_cell_cases hstd v with hv | ⟨d, hd, _⟩
      · subst v
        simp at hrow
      · subst v
        simp at hrow
    · subst u
      rcases standardShape_cell_cases hstd v with hv | ⟨d, hd, _⟩
      · subst v
        have hn : 0 < n := by
          have := hstd.1
          omega
        letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
        let c0 : Fin n := ⟨0, hn⟩
        have hc0 : c = c0 := by
          apply Fin.ext
          simpa [c0] using hcol
        subst c
        simp only [Function.comp_apply, standardShapeCellEquiv_symm_top,
          standardShapeCellEquiv_symm_lower, standardShapeLabelMap]
        change p.succAbove c0 < p
        have hc0_eq : c0 = 0 := by ext; simp [c0]
        rw [hc0_eq]
        rw [Fin.succAbove_ne_zero_zero hp]
        exact Fin.pos_iff_ne_zero.mpr hp
      · subst v
        simp at hrow

@[simp] theorem standardTableauWithLowerEntry_lower {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (p : Fin (n + 1)) (hp : p ≠ 0) :
    standardLowerEntry hstd (standardTableauWithLowerEntry hstd p hp) = p := by
  unfold standardLowerEntry standardTableauWithLowerEntry
  change standardShapeLabelMap p
    ((standardShapeCellEquiv hstd).symm (standardLowerCell hstd)) = p
  simp [standardShapeLabelMap]

@[simp] theorem standardTableauWithLowerEntry_top {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (p : Fin (n + 1)) (hp : p ≠ 0) (c : Fin n) :
    (standardTableauWithLowerEntry hstd p hp).entry
      (standardTopCell hstd c) = p.succAbove c := by
  unfold standardTableauWithLowerEntry
  change standardShapeLabelMap p
    ((standardShapeCellEquiv hstd).symm (standardTopCell hstd c)) = _
  simp [standardShapeLabelMap]

/-- Index standard-shape tableaux by the possible positive lower entries. -/
noncomputable def standardTableauOfIndex {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (k : Fin n) :
    StandardYoungTableau lam :=
  standardTableauWithLowerEntry hstd k.succ (by simp)

/-- Recover the zero-based index from a standard tableau's positive lower
entry. -/
def standardTableauIndex {n : Nat} {lam : YoungDiagram (n + 1)}
    (hstd : IsStandard lam) (T : StandardYoungTableau lam) : Fin n :=
  (standardLowerEntry hstd T).pred (standardLowerEntry_ne_zero hstd T)

@[simp] theorem standardTableauIndex_tableauOfIndex {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (k : Fin n) :
    standardTableauIndex hstd (standardTableauOfIndex hstd k) = k := by
  apply Fin.ext
  simp [standardTableauIndex, standardTableauOfIndex]

@[simp] theorem standardTableauOfIndex_tableauIndex {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) :
    standardTableauOfIndex hstd (standardTableauIndex hstd T) = T := by
  apply standardYoungTableau_eq_of_lowerEntry_eq hstd
  simp [standardTableauOfIndex, standardTableauIndex]

/-- The canonical equivalence between positive lower entries and standard
tableaux of shape `(n,1)`. -/
noncomputable def standardTableauEquivFin {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    Fin n ≃ StandardYoungTableau lam where
  toFun := standardTableauOfIndex hstd
  invFun := standardTableauIndex hstd
  left_inv := standardTableauIndex_tableauOfIndex hstd
  right_inv := standardTableauOfIndex_tableauIndex hstd

/-! ## A triangular coordinate model of the standard representation -/

/-- The diagonal coefficient for the adjacent transposition at zero-based
position `a` in the degree-one coordinate model. -/
def degreeOneDiag (a : Nat) : Real := ((a + 1 : Nat) : Real)⁻¹

/-- The corresponding nonnegative off-diagonal coefficient. -/
noncomputable def degreeOneOff (a : Nat) : Real :=
  Real.sqrt (1 - degreeOneDiag a ^ 2)

theorem degreeOneDiag_pos (a : Nat) : 0 < degreeOneDiag a := by
  unfold degreeOneDiag
  positivity

theorem degreeOneDiag_le_one (a : Nat) : degreeOneDiag a ≤ 1 := by
  rw [degreeOneDiag, inv_le_one₀]
  · norm_num
  · positivity

theorem degreeOneDiag_lt_one {a : Nat} (ha : 1 ≤ a) :
    degreeOneDiag a < 1 := by
  rw [degreeOneDiag, inv_lt_one₀]
  · exact_mod_cast (show 1 < a + 1 by omega)
  · positivity

theorem degreeOneOff_sq (a : Nat) :
    degreeOneOff a ^ 2 = 1 - degreeOneDiag a ^ 2 := by
  rw [degreeOneOff, Real.sq_sqrt]
  have hp := degreeOneDiag_pos a
  have hl := degreeOneDiag_le_one a
  nlinarith

theorem degreeOneDiag_sq_add_off_sq (a : Nat) :
    degreeOneDiag a ^ 2 + degreeOneOff a ^ 2 = 1 := by
  rw [degreeOneOff_sq]
  ring

theorem degreeOneOff_pos {a : Nat} (ha : 1 ≤ a) :
    0 < degreeOneOff a := by
  unfold degreeOneOff
  apply Real.sqrt_pos.2
  have hp := degreeOneDiag_pos a
  have hl := degreeOneDiag_lt_one ha
  nlinarith

theorem degreeOneOff_ne_zero {a : Nat} (ha : 1 ≤ a) :
    degreeOneOff a ≠ 0 :=
  ne_of_gt (degreeOneOff_pos ha)

theorem degreeOneDiag_mul_succ (a : Nat) :
    degreeOneDiag a * (a + 1 : Nat) = 1 := by
  rw [degreeOneDiag]
  field_simp

theorem one_sub_degreeOneDiag (a : Nat) :
    1 - degreeOneDiag (a + 1) =
      (a + 1 : Nat) * degreeOneDiag (a + 1) := by
  rw [degreeOneDiag]
  push_cast
  field_simp
  ring

/-- Recursive scale of the triangular standard-coordinate basis. -/
noncomputable def degreeOneAmplitude : Nat → Real
  | 0 => 1
  | k + 1 =>
      degreeOneAmplitude k * (1 - degreeOneDiag (k + 1)) /
        degreeOneOff (k + 1)

theorem degreeOneAmplitude_ne_zero (k : Nat) :
    degreeOneAmplitude k ≠ 0 := by
  induction k with
  | zero => simp [degreeOneAmplitude]
  | succ k ih =>
      rw [degreeOneAmplitude]
      apply div_ne_zero
      · apply mul_ne_zero ih
        have hp := degreeOneDiag_pos (k + 1)
        have hl := degreeOneDiag_lt_one (a := k + 1) (by omega)
        nlinarith
      · exact degreeOneOff_ne_zero (by omega)

/-- A triangular basis vector for the sum-zero coordinate representation.
Its first `k+1` coordinates are equal, its next coordinate is their negative
sum, and all later coordinates vanish. -/
noncomputable def degreeOneCoordinateVector (k : Nat) : Nat → Real :=
  fun j =>
    if j ≤ k then degreeOneAmplitude k
    else if j = k + 1 then -((k + 1 : Nat) : Real) * degreeOneAmplitude k
    else 0

@[simp] theorem degreeOneCoordinateVector_of_le (k j : Nat) (hj : j ≤ k) :
    degreeOneCoordinateVector k j = degreeOneAmplitude k := by
  simp [degreeOneCoordinateVector, hj]

@[simp] theorem degreeOneCoordinateVector_last (k : Nat) :
    degreeOneCoordinateVector k (k + 1) =
      -((k + 1 : Nat) : Real) * degreeOneAmplitude k := by
  simp [degreeOneCoordinateVector]

@[simp] theorem degreeOneCoordinateVector_of_lt {k j : Nat}
    (hj : k + 1 < j) :
    degreeOneCoordinateVector k j = 0 := by
  unfold degreeOneCoordinateVector
  rw [if_neg (by omega), if_neg (by omega)]

/-- Swap neighboring natural-number coordinates. -/
def natAdjacentCoordinateSwap (a : Nat) (v : Nat → Real) : Nat → Real :=
  fun j => if j = a then v (a + 1) else if j = a + 1 then v a else v j

@[simp] theorem natAdjacentCoordinateSwap_left (a : Nat) (v : Nat → Real) :
    natAdjacentCoordinateSwap a v a = v (a + 1) := by
  simp [natAdjacentCoordinateSwap]

@[simp] theorem natAdjacentCoordinateSwap_right (a : Nat) (v : Nat → Real) :
    natAdjacentCoordinateSwap a v (a + 1) = v a := by
  simp [natAdjacentCoordinateSwap]

theorem natAdjacentCoordinateSwap_of_ne (a j : Nat) (v : Nat → Real)
    (hja : j ≠ a) (hjs : j ≠ a + 1) :
    natAdjacentCoordinateSwap a v j = v j := by
  simp [natAdjacentCoordinateSwap, hja, hjs]

theorem natAdjacentCoordinateSwap_involutive (a : Nat) (v : Nat → Real) :
    natAdjacentCoordinateSwap a (natAdjacentCoordinateSwap a v) = v := by
  funext j
  by_cases hja : j = a
  · subst j
    simp
  · by_cases hjs : j = a + 1
    · subst j
      simp
    · simp [natAdjacentCoordinateSwap, hja, hjs]

theorem natAdjacentCoordinateSwap_add (a : Nat) (v w : Nat → Real) :
    natAdjacentCoordinateSwap a (fun j => v j + w j) =
      fun j => natAdjacentCoordinateSwap a v j +
        natAdjacentCoordinateSwap a w j := by
  funext j
  by_cases hja : j = a
  · simp [natAdjacentCoordinateSwap, hja]
  · by_cases hjs : j = a + 1
    · simp [natAdjacentCoordinateSwap, hjs]
    · simp [natAdjacentCoordinateSwap, hja, hjs]

theorem natAdjacentCoordinateSwap_smul (a : Nat) (c : Real)
    (v : Nat → Real) :
    natAdjacentCoordinateSwap a (fun j => c * v j) =
      fun j => c * natAdjacentCoordinateSwap a v j := by
  funext j
  by_cases hja : j = a
  · simp [natAdjacentCoordinateSwap, hja]
  · by_cases hjs : j = a + 1
    · simp [natAdjacentCoordinateSwap, hjs]
    · simp [natAdjacentCoordinateSwap, hja, hjs]

theorem degreeOneOff_mul_amplitude_succ (k : Nat) :
    degreeOneOff (k + 1) * degreeOneAmplitude (k + 1) =
      degreeOneAmplitude k * (1 - degreeOneDiag (k + 1)) := by
  rw [degreeOneAmplitude]
  field_simp [degreeOneOff_ne_zero (a := k + 1) (by omega)]

/-- The adjacent swap immediately to the right of vector `k` mixes it with
vector `k+1` by the Young orthogonal coefficients. -/
theorem natAdjacentCoordinateSwap_degreeOneCoordinateVector_right
    (k : Nat) :
    natAdjacentCoordinateSwap (k + 1) (degreeOneCoordinateVector k) =
      fun j =>
        degreeOneDiag (k + 1) * degreeOneCoordinateVector k j +
          degreeOneOff (k + 1) * degreeOneCoordinateVector (k + 1) j := by
  funext j
  by_cases hj0 : j ≤ k
  · have hj_ne_a : j ≠ k + 1 := by omega
    have hj_ne_s : j ≠ k + 2 := by omega
    rw [natAdjacentCoordinateSwap_of_ne _ _ _ hj_ne_a hj_ne_s,
      degreeOneCoordinateVector_of_le _ _ hj0,
      degreeOneCoordinateVector_of_le _ _ (by omega),
      degreeOneOff_mul_amplitude_succ]
    ring
  · by_cases hj1 : j = k + 1
    · subst j
      rw [natAdjacentCoordinateSwap_left,
        degreeOneCoordinateVector_of_lt (by omega),
        degreeOneCoordinateVector_last,
        degreeOneCoordinateVector_of_le _ _ (by omega),
        degreeOneOff_mul_amplitude_succ,
        one_sub_degreeOneDiag]
      push_cast
      ring
    · by_cases hj2 : j = k + 2
      · subst j
        rw [natAdjacentCoordinateSwap_right,
          degreeOneCoordinateVector_last,
          degreeOneCoordinateVector_of_lt (by omega),
          degreeOneCoordinateVector_last]
        rw [show degreeOneOff (k + 1) *
              (-((k + 1 + 1 : Nat) : Real) * degreeOneAmplitude (k + 1)) =
            -((k + 2 : Nat) : Real) *
              (degreeOneOff (k + 1) * degreeOneAmplitude (k + 1)) by
              push_cast; ring,
          degreeOneOff_mul_amplitude_succ]
        have hd := degreeOneDiag_mul_succ (k + 1)
        have hs := one_sub_degreeOneDiag k
        push_cast at hd hs ⊢
        have hid :
            (k + 2 : Real) * (1 - degreeOneDiag (k + 1)) = k + 1 := by
          rw [hs]
          have hd' : degreeOneDiag (k + 1) * (k + 2 : Real) = 1 := by
            rw [show (k + 2 : Real) = (k : Real) + 1 + 1 by ring]
            exact hd
          calc
            (k + 2 : Real) *
                ((k + 1 : Real) * degreeOneDiag (k + 1)) =
                (k + 1 : Real) *
                  (degreeOneDiag (k + 1) * (k + 2 : Real)) := by ring
            _ = k + 1 := by rw [hd']; ring
        rw [← hid]
        ring
      · have hjgt : k + 2 < j := by omega
        rw [natAdjacentCoordinateSwap_of_ne _ _ _ hj1 hj2,
          degreeOneCoordinateVector_of_lt (by omega),
          degreeOneCoordinateVector_of_lt (by omega)]
        ring

/-- The same two-dimensional swap formula in the reverse basis direction. -/
theorem natAdjacentCoordinateSwap_degreeOneCoordinateVector_left
    (k : Nat) :
    natAdjacentCoordinateSwap (k + 1) (degreeOneCoordinateVector (k + 1)) =
      fun j =>
        degreeOneOff (k + 1) * degreeOneCoordinateVector k j -
          degreeOneDiag (k + 1) * degreeOneCoordinateVector (k + 1) j := by
  let d := degreeOneDiag (k + 1)
  let s := degreeOneOff (k + 1)
  let v := degreeOneCoordinateVector k
  let w := degreeOneCoordinateVector (k + 1)
  have hright : natAdjacentCoordinateSwap (k + 1) v =
      fun j => d * v j + s * w j := by
    simpa [d, s, v, w] using
      natAdjacentCoordinateSwap_degreeOneCoordinateVector_right k
  have hswapped := congrArg (natAdjacentCoordinateSwap (k + 1)) hright
  rw [natAdjacentCoordinateSwap_involutive,
    natAdjacentCoordinateSwap_add] at hswapped
  rw [natAdjacentCoordinateSwap_smul,
    natAdjacentCoordinateSwap_smul] at hswapped
  funext j
  have hj := congrFun hswapped j
  have hrj := congrFun hright j
  have hsquare := degreeOneDiag_sq_add_off_sq (k + 1)
  have hspos := degreeOneOff_pos (a := k + 1) (by omega)
  dsimp [d, s, v, w] at hj hrj ⊢
  rw [hrj] at hj
  have hmul :
      degreeOneOff (k + 1) *
          natAdjacentCoordinateSwap (k + 1)
            (degreeOneCoordinateVector (k + 1)) j =
        degreeOneOff (k + 1) *
          (degreeOneOff (k + 1) * degreeOneCoordinateVector k j -
            degreeOneDiag (k + 1) *
              degreeOneCoordinateVector (k + 1) j) := by
    calc
      degreeOneOff (k + 1) *
          natAdjacentCoordinateSwap (k + 1)
            (degreeOneCoordinateVector (k + 1)) j =
          degreeOneCoordinateVector k j -
            degreeOneDiag (k + 1) *
              (degreeOneDiag (k + 1) * degreeOneCoordinateVector k j +
                degreeOneOff (k + 1) *
                  degreeOneCoordinateVector (k + 1) j) := by linarith
      _ = degreeOneOff (k + 1) *
          (degreeOneOff (k + 1) * degreeOneCoordinateVector k j -
            degreeOneDiag (k + 1) *
              degreeOneCoordinateVector (k + 1) j) := by
            have hrepl : degreeOneCoordinateVector k j =
                (degreeOneDiag (k + 1) ^ 2 +
                  degreeOneOff (k + 1) ^ 2) *
                    degreeOneCoordinateVector k j := by
              rw [hsquare]
              ring
            nth_rewrite 1 [hrepl]
            ring
  exact mul_left_cancel₀ (ne_of_gt hspos) hmul

/-- Earlier adjacent swaps fix a later triangular basis vector. -/
theorem natAdjacentCoordinateSwap_degreeOneCoordinateVector_of_lt
    {a k : Nat} (hak : a < k) :
    natAdjacentCoordinateSwap a (degreeOneCoordinateVector k) =
      degreeOneCoordinateVector k := by
  funext j
  by_cases hja : j = a
  · subst j
    rw [natAdjacentCoordinateSwap_left,
      degreeOneCoordinateVector_of_le _ _ (by omega),
      degreeOneCoordinateVector_of_le _ _ (by omega)]
  · by_cases hjs : j = a + 1
    · subst j
      rw [natAdjacentCoordinateSwap_right,
        degreeOneCoordinateVector_of_le _ _ (by omega),
        degreeOneCoordinateVector_of_le _ _ (by omega)]
    · exact natAdjacentCoordinateSwap_of_ne a j _ hja hjs

/-- Adjacent swaps beyond the support fix a triangular basis vector. -/
theorem natAdjacentCoordinateSwap_degreeOneCoordinateVector_of_gt
    {a k : Nat} (hka : k + 1 < a) :
    natAdjacentCoordinateSwap a (degreeOneCoordinateVector k) =
      degreeOneCoordinateVector k := by
  funext j
  by_cases hja : j = a
  · subst j
    rw [natAdjacentCoordinateSwap_left,
      degreeOneCoordinateVector_of_lt (by omega),
      degreeOneCoordinateVector_of_lt (by omega)]
  · by_cases hjs : j = a + 1
    · subst j
      rw [natAdjacentCoordinateSwap_right,
        degreeOneCoordinateVector_of_lt (by omega),
        degreeOneCoordinateVector_of_lt (by omega)]
    · exact natAdjacentCoordinateSwap_of_ne a j _ hja hjs

/-- The first coordinate swap negates the first standard basis vector. -/
theorem natAdjacentCoordinateSwap_degreeOneCoordinateVector_zero :
    natAdjacentCoordinateSwap 0 (degreeOneCoordinateVector 0) =
      fun j => -degreeOneCoordinateVector 0 j := by
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [degreeOneCoordinateVector, natAdjacentCoordinateSwap,
      degreeOneAmplitude]
  · by_cases hj1 : j = 1
    · subst j
      simp [degreeOneCoordinateVector, natAdjacentCoordinateSwap,
        degreeOneAmplitude]
    · have hjgt : 1 < j := by omega
      rw [natAdjacentCoordinateSwap_of_ne 0 j _ (by omega) (by omega),
        degreeOneCoordinateVector_of_lt hjgt]
      simp

/-- Synthesize a coordinate vector from a constant coefficient and the
triangular degree-one coordinates. -/
noncomputable def degreeOneCoordinateSynthesis (n : Nat) :
    (Real × (Fin n → Real)) →ₗ[Real] (Fin (n + 1) → Real) where
  toFun cf := fun j =>
    cf.1 + ∑ k : Fin n,
      cf.2 k * degreeOneCoordinateVector k j
  map_add' := by
    intro x y
    funext j
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c x
    funext j
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simp only [RingHom.id_apply]
    ring

theorem degreeOneCoordinateSynthesis_injective (n : Nat) :
    Function.Injective (degreeOneCoordinateSynthesis n) := by
  intro x y hxy
  have hz : degreeOneCoordinateSynthesis n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let c := (x - y).1
  let f := (x - y).2
  have hpoint : ∀ j : Fin (n + 1),
      c + ∑ k : Fin n,
        f k * degreeOneCoordinateVector k j = 0 := by
    intro j
    have := congrFun hz j
    simpa [degreeOneCoordinateSynthesis, c, f] using this
  have hf : ∀ k : Nat, (hk : k < n) → f ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let ik : Fin n := ⟨k, hk⟩
        let jk : Fin (n + 1) := ⟨k, by omega⟩
        let js : Fin (n + 1) := ⟨k + 1, by omega⟩
        have hkpoint := hpoint jk
        have hspoint := hpoint js
        have hdiff :
            (∑ r : Fin n,
              f r * (degreeOneCoordinateVector r jk -
                degreeOneCoordinateVector r js)) = 0 := by
          calc
            (∑ r : Fin n,
                f r * (degreeOneCoordinateVector r jk -
                  degreeOneCoordinateVector r js)) =
                (∑ r : Fin n, f r * degreeOneCoordinateVector r jk) -
                  ∑ r : Fin n, f r * degreeOneCoordinateVector r js := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro r _
                    ring
            _ = 0 := by linarith
        have hother : ∀ r : Fin n, r ≠ ik →
            f r * (degreeOneCoordinateVector r jk -
              degreeOneCoordinateVector r js) = 0 := by
          intro r hri
          by_cases hrk : (r : Nat) < k
          · rw [ih (r : Nat) hrk r.isLt]
            ring
          · have hkr : k < (r : Nat) := by
              have : (r : Nat) ≠ k := by
                intro heq
                apply hri
                apply Fin.ext
                simpa [ik] using heq
              omega
            have hkj : k ≤ (r : Nat) := Nat.le_of_lt hkr
            have hsj : k + 1 ≤ (r : Nat) := by omega
            rw [degreeOneCoordinateVector_of_le _ _ (by simpa [jk] using hkj),
              degreeOneCoordinateVector_of_le _ _ (by simpa [js] using hsj)]
            ring
        have hsingle :
            (∑ r : Fin n,
              f r * (degreeOneCoordinateVector r jk -
                degreeOneCoordinateVector r js)) =
              f ik * (degreeOneCoordinateVector ik jk -
                degreeOneCoordinateVector ik js) := by
          rw [Fintype.sum_eq_single ik]
          intro r hr
          exact hother r hr
        rw [hsingle] at hdiff
        have hamp := degreeOneAmplitude_ne_zero k
        have hfactor :
            degreeOneCoordinateVector k k -
                degreeOneCoordinateVector k (k + 1) =
              (k + 2 : Real) * degreeOneAmplitude k := by
          rw [degreeOneCoordinateVector_of_le _ _ (by omega),
            degreeOneCoordinateVector_last]
          push_cast
          ring
        change f ik *
          (degreeOneCoordinateVector k k -
            degreeOneCoordinateVector k (k + 1)) = 0 at hdiff
        rw [hfactor] at hdiff
        have hpos : (0 : Real) < k + 2 := by positivity
        exact (mul_eq_zero.mp hdiff).resolve_right
          (mul_ne_zero (ne_of_gt hpos) hamp)
  have hfzero : f = 0 := by
    funext k
    exact hf k k.isLt
  have hc : c = 0 := by
    have h0 := hpoint 0
    simp [hfzero] at h0
    exact h0
  have hsub : x - y = 0 := by
    apply Prod.ext
    · simpa [c] using hc
    · simpa [f] using hfzero
  exact sub_eq_zero.mp hsub

/-- The constant vector together with the triangular degree-one vectors is a
basis of the full permutation-coordinate space. -/
noncomputable def degreeOneCoordinateEquiv (n : Nat) :
    (Real × (Fin n → Real)) ≃ₗ[Real] (Fin (n + 1) → Real) := by
  let L := degreeOneCoordinateSynthesis n
  have hinj : Function.Injective L := degreeOneCoordinateSynthesis_injective n
  have hdim : Module.finrank Real (Real × (Fin n → Real)) =
      Module.finrank Real (Fin (n + 1) → Real) := by
    simp [Nat.add_comm]
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact LinearEquiv.ofBijective L ⟨hinj, hsurj⟩

/-! ## Adjacent swaps on standard-shape tableaux -/

theorem standardCell_row_eq_zero_of_entry_ne_lower {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (u : YoungCell lam)
    (hu : T.entry u ≠ standardLowerEntry hstd T) :
    YoungCell.row u = 0 := by
  rcases standardShape_cell_cases hstd u with hlow | ⟨c, hc, _⟩
  · subst u
    exact False.elim (hu rfl)
  · subst u
    simp

theorem adjacentSameRow_of_lowerEntry_ne {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hlo : standardLowerEntry hstd T ≠ adjacentEntryLo a)
    (hhi : standardLowerEntry hstd T ≠ adjacentEntryHi a) :
    adjacentSameRow T a := by
  have hlo0 : YoungCell.row (adjacentLoCell T a) = 0 :=
    standardCell_row_eq_zero_of_entry_ne_lower hstd T _ (by
      intro h
      apply hlo
      rw [← h, entry_adjacentLoCell])
  have hhi0 : YoungCell.row (adjacentHiCell T a) = 0 :=
    standardCell_row_eq_zero_of_entry_ne_lower hstd T _ (by
      intro h
      apply hhi
      rw [← h, entry_adjacentHiCell])
  unfold adjacentSameRow
  rw [hlo0, hhi0]

theorem standardTopCell_entry_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    T.entry (standardTopCell hstd a) = adjacentEntryLo a := by
  rw [standardTopCell_entry_eq_succAbove hstd T a, hp]
  change a.succ.succAbove a = a.castSucc
  exact Fin.succAbove_succ_self a

theorem standardTopCell_entry_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    T.entry (standardTopCell hstd a) = adjacentEntryHi a := by
  rw [standardTopCell_entry_eq_succAbove hstd T a, hp]
  change a.castSucc.succAbove a = a.succ
  exact Fin.succAbove_castSucc_self a

theorem adjacentHiCell_eq_standardLowerCell_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    adjacentHiCell T a = standardLowerCell hstd := by
  apply T.bijective.1
  rw [entry_adjacentHiCell]
  exact hp.symm

theorem adjacentLoCell_eq_standardTopCell_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    adjacentLoCell T a = standardTopCell hstd a := by
  apply T.bijective.1
  rw [entry_adjacentLoCell]
  exact (standardTopCell_entry_of_lowerEntry_eq_hi hstd T a hp).symm

theorem adjacentLoCell_eq_standardLowerCell_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    adjacentLoCell T a = standardLowerCell hstd := by
  apply T.bijective.1
  rw [entry_adjacentLoCell]
  exact hp.symm

theorem adjacentHiCell_eq_standardTopCell_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    adjacentHiCell T a = standardTopCell hstd a := by
  apply T.bijective.1
  rw [entry_adjacentHiCell]
  exact (standardTopCell_entry_of_lowerEntry_eq_lo hstd T a hp).symm

theorem adjacentSameCol_of_lowerEntry_eq_hi_zero {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a)
    (ha : (a : Nat) = 0) :
    adjacentSameCol T a := by
  unfold adjacentSameCol
  rw [adjacentLoCell_eq_standardTopCell_of_lowerEntry_eq_hi hstd T a hp,
    adjacentHiCell_eq_standardLowerCell_of_lowerEntry_eq_hi hstd T a hp]
  simp [ha]

theorem not_adjacentSameCol_of_lowerEntry_eq_hi_pos {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a)
    (ha : 0 < (a : Nat)) :
    ¬ adjacentSameCol T a := by
  unfold adjacentSameCol
  rw [adjacentLoCell_eq_standardTopCell_of_lowerEntry_eq_hi hstd T a hp,
    adjacentHiCell_eq_standardLowerCell_of_lowerEntry_eq_hi hstd T a hp]
  simp
  omega

theorem not_adjacentSameRow_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    ¬ adjacentSameRow T a := by
  unfold adjacentSameRow
  rw [adjacentLoCell_eq_standardTopCell_of_lowerEntry_eq_hi hstd T a hp,
    adjacentHiCell_eq_standardLowerCell_of_lowerEntry_eq_hi hstd T a hp]
  simp

theorem not_adjacentSameRow_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    ¬ adjacentSameRow T a := by
  unfold adjacentSameRow
  rw [adjacentLoCell_eq_standardLowerCell_of_lowerEntry_eq_lo hstd T a hp,
    adjacentHiCell_eq_standardTopCell_of_lowerEntry_eq_lo hstd T a hp]
  simp

theorem not_adjacentSameCol_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    ¬ adjacentSameCol T a := by
  have hpzero := standardLowerEntry_ne_zero hstd T
  have ha : 0 < (a : Nat) := by
    by_contra hnot
    have ha0 : (a : Nat) = 0 := by omega
    apply hpzero
    apply Fin.ext
    simp [hp, adjacentEntryLo, ha0]
  unfold adjacentSameCol
  rw [adjacentLoCell_eq_standardLowerCell_of_lowerEntry_eq_lo hstd T a hp,
    adjacentHiCell_eq_standardTopCell_of_lowerEntry_eq_lo hstd T a hp]
  simp
  omega

theorem adjacentAxialDistance_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    adjacentAxialDistance T a = -((a : Nat) + 1 : Int) := by
  have hp' : T.entry (standardLowerCell hstd) = adjacentEntryHi a := by
    simpa [standardLowerEntry] using hp
  unfold adjacentAxialDistance entryContent
  rw [cellOfEntry_eq_of_entry T
      (standardTopCell_entry_of_lowerEntry_eq_hi hstd T a hp),
    cellOfEntry_eq_of_entry T hp']
  simp [YoungCell.content]
  ring

theorem adjacentAxialDistance_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    adjacentAxialDistance T a = ((a : Nat) + 1 : Int) := by
  have hp' : T.entry (standardLowerCell hstd) = adjacentEntryLo a := by
    simpa [standardLowerEntry] using hp
  unfold adjacentAxialDistance entryContent
  rw [cellOfEntry_eq_of_entry T
      (standardTopCell_entry_of_lowerEntry_eq_lo hstd T a hp),
    cellOfEntry_eq_of_entry T hp']
  simp [YoungCell.content]

theorem youngAdjacentDiagCoeff_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    youngAdjacentDiagCoeff T a = -degreeOneDiag a := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_of_lowerEntry_eq_hi hstd T a hp]
  unfold degreeOneDiag
  push_cast
  rw [inv_neg]

theorem youngAdjacentDiagCoeff_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    youngAdjacentDiagCoeff T a = degreeOneDiag a := by
  rw [youngAdjacentDiagCoeff,
    adjacentAxialDistance_of_lowerEntry_eq_lo hstd T a hp]
  unfold degreeOneDiag
  push_cast
  rfl

theorem youngAdjacentOffCoeff_of_lowerEntry_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a) :
    youngAdjacentOffCoeff T a = degreeOneOff a := by
  rw [youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_of_lowerEntry_eq_hi hstd T a hp]
  simp [degreeOneOff]

theorem youngAdjacentOffCoeff_of_lowerEntry_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a) :
    youngAdjacentOffCoeff T a = degreeOneOff a := by
  rw [youngAdjacentOffCoeff,
    youngAdjacentDiagCoeff_of_lowerEntry_eq_lo hstd T a hp]
  rfl

theorem standardLowerEntry_adjacentSwap_eq_lo_of_eq_hi {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryHi a)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    standardLowerEntry hstd (adjacentSwapTableau T a hrow hcol) =
      adjacentEntryLo a := by
  have hcell := adjacentHiCell_eq_standardLowerCell_of_lowerEntry_eq_hi
    hstd T a hp
  unfold standardLowerEntry adjacentSwapTableau
  change adjacentSwapEntry T a (standardLowerCell hstd) = adjacentEntryLo a
  rw [← hcell]
  exact adjacentSwapEntry_hiCell T a

theorem standardLowerEntry_adjacentSwap_eq_hi_of_eq_lo {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) (a : Fin n)
    (hp : standardLowerEntry hstd T = adjacentEntryLo a)
    (hrow : ¬ adjacentSameRow T a) (hcol : ¬ adjacentSameCol T a) :
    standardLowerEntry hstd (adjacentSwapTableau T a hrow hcol) =
      adjacentEntryHi a := by
  have hcell := adjacentLoCell_eq_standardLowerCell_of_lowerEntry_eq_lo
    hstd T a hp
  unfold standardLowerEntry adjacentSwapTableau
  change adjacentSwapEntry T a (standardLowerCell hstd) = adjacentEntryHi a
  rw [← hcell]
  exact adjacentSwapEntry_loCell T a

@[simp] theorem standardLowerEntry_standardTableauOfIndex {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (k : Fin n) :
    standardLowerEntry hstd (standardTableauOfIndex hstd k) = k.succ := by
  simp [standardTableauOfIndex]

/-- Restrict a triangular degree-one vector to the coordinate set
`Fin (n+1)`. -/
noncomputable def degreeOneFinVector {n : Nat} (k : Fin n) :
    Fin (n + 1) → Real :=
  fun j => degreeOneCoordinateVector k j

/-- Every triangular degree-one basis vector has coordinate sum zero. -/
theorem degreeOneFinVector_sum_eq_zero {n : Nat} (k : Fin n) :
    ∑ j : Fin (n + 1), degreeOneFinVector k j = 0 := by
  change (∑ j : Fin (n + 1),
    degreeOneCoordinateVector (k : Nat) (j : Nat)) = 0
  rw [Fin.sum_univ_eq_sum_range]
  have hsubset : Finset.range ((k : Nat) + 2) ⊆
      Finset.range (n + 1) := Finset.range_mono (by omega)
  have htail : ∀ j ∈ Finset.range (n + 1),
      j ∉ Finset.range ((k : Nat) + 2) →
        degreeOneCoordinateVector (k : Nat) j = 0 := by
    intro j _hj hjnot
    have hjgt : (k : Nat) + 1 < j := by
      simp only [Finset.mem_range, not_lt] at hjnot
      omega
    exact degreeOneCoordinateVector_of_lt hjgt
  rw [← Finset.sum_subset hsubset htail]
  rw [Finset.sum_range_succ]
  have hfirst :
      (∑ j ∈ Finset.range ((k : Nat) + 1),
        degreeOneCoordinateVector (k : Nat) j) =
        ((k : Nat) + 1 : Real) * degreeOneAmplitude k := by
    calc
      (∑ j ∈ Finset.range ((k : Nat) + 1),
          degreeOneCoordinateVector (k : Nat) j) =
          ∑ _j ∈ Finset.range ((k : Nat) + 1),
            degreeOneAmplitude k := by
        apply Finset.sum_congr rfl
        intro j hj
        apply degreeOneCoordinateVector_of_le
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      _ = ((k : Nat) + 1 : Real) * degreeOneAmplitude k := by
        simp
  rw [hfirst]
  rw [degreeOneCoordinateVector_last]
  push_cast
  ring

/-- A literal adjacent permutation acts by the corresponding neighboring
coordinate swap. -/
theorem permutationCoordinateRho_adjacent_degreeOneFinVector {n : Nat}
    (a k : Fin n) :
    permutationCoordinateRho (appA_adjacentTransposition a)
        (degreeOneFinVector k) =
      fun j : Fin (n + 1) =>
        natAdjacentCoordinateSwap a (degreeOneCoordinateVector k) j := by
  funext j
  simp only [permutationCoordinateRho, appA_adjacentTransposition]
  by_cases hja : j = Fin.castSucc a
  · subst j
    simp [degreeOneFinVector, natAdjacentCoordinateSwap]
  · by_cases hjs : j = Fin.succ a
    · subst j
      simp [degreeOneFinVector, natAdjacentCoordinateSwap]
    · have hja' : (j : Nat) ≠ (a : Nat) := by
        intro h
        apply hja
        apply Fin.ext
        simpa using h
      have hjs' : (j : Nat) ≠ (a : Nat) + 1 := by
        intro h
        apply hjs
        apply Fin.ext
        simpa using h
      rw [Equiv.symm_swap]
      rw [Equiv.swap_apply_of_ne_of_ne hja hjs]
      simp [degreeOneFinVector, natAdjacentCoordinateSwap, hja', hjs']

/-- Send tableau coordinates of a standard shape to the triangular coordinate
model. -/
noncomputable def standardCoordinateMap {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    TableauSpace lam →ₗ[Real] (Fin (n + 1) → Real) where
  toFun f := fun j => ∑ T : StandardYoungTableau lam,
    f T * degreeOneFinVector (standardTableauIndex hstd T) j
  map_add' := by
    intro f g
    funext j
    simp_rw [Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]

/-- The triangular standard-coordinate map lands in the literal sum-zero
subspace. -/
theorem standardCoordinateMap_mem_sumZero {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (f : TableauSpace lam) :
    standardCoordinateMap hstd f ∈
      permutationCoordinateSumZero (n + 1) := by
  change (∑ j : Fin (n + 1), standardCoordinateMap hstd f j) = 0
  change (∑ j : Fin (n + 1),
      ∑ T : StandardYoungTableau lam,
        f T * degreeOneFinVector (standardTableauIndex hstd T) j) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro T _
  rw [← Finset.mul_sum]
  rw [degreeOneFinVector_sum_eq_zero]
  simp

@[simp] theorem standardCoordinateMap_tableauBasisVec {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (T : StandardYoungTableau lam) :
    standardCoordinateMap hstd (tableauBasisVec T) =
      degreeOneFinVector (standardTableauIndex hstd T) := by
  funext j
  change (∑ S : StandardYoungTableau lam,
      tableauBasisVec T S *
        degreeOneFinVector (standardTableauIndex hstd S) j) = _
  rw [Fintype.sum_eq_single T]
  · simp [tableauBasisVec]
  · intro S hST
    simp [tableauBasisVec, hST]

@[simp] theorem standardCoordinateMap_tableauBasisVec_index {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) (k : Fin n) :
    standardCoordinateMap hstd
        (tableauBasisVec (standardTableauOfIndex hstd k)) =
      degreeOneFinVector k := by
  rw [standardCoordinateMap_tableauBasisVec]
  simp

/-- The triangular coordinate map intertwines one adjacent Young operator on
each standard tableau basis vector. -/
theorem standardCoordinateMap_youngAdjacentOperator_basis {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (a k : Fin n) :
    standardCoordinateMap hstd
        (youngAdjacentOperator a
          (tableauBasisVec (standardTableauOfIndex hstd k))) =
      permutationCoordinateRho (appA_adjacentTransposition a)
        (standardCoordinateMap hstd
          (tableauBasisVec (standardTableauOfIndex hstd k))) := by
  let T := standardTableauOfIndex hstd k
  by_cases hak : (a : Nat) < (k : Nat)
  · have hrow : adjacentSameRow T a := by
      apply adjacentSameRow_of_lowerEntry_ne hstd
      · intro h
        have hv := congrArg Fin.val h
        simp [T, adjacentEntryLo] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        simp [T, adjacentEntryHi] at hv
        omega
    rw [youngAdjacentOperator_basis_sameRow T a hrow,
      standardCoordinateMap_tableauBasisVec_index,
      permutationCoordinateRho_adjacent_degreeOneFinVector]
    have hfix :=
      natAdjacentCoordinateSwap_degreeOneCoordinateVector_of_lt hak
    funext j
    simpa [degreeOneFinVector] using (congrFun hfix j).symm
  · by_cases hka : (k : Nat) + 1 < (a : Nat)
    · have hrow : adjacentSameRow T a := by
        apply adjacentSameRow_of_lowerEntry_ne hstd
        · intro h
          have hv := congrArg Fin.val h
          simp [T, adjacentEntryLo] at hv
          omega
        · intro h
          have hv := congrArg Fin.val h
          simp [T, adjacentEntryHi] at hv
          omega
      rw [youngAdjacentOperator_basis_sameRow T a hrow,
        standardCoordinateMap_tableauBasisVec_index,
        permutationCoordinateRho_adjacent_degreeOneFinVector]
      have hfix :=
        natAdjacentCoordinateSwap_degreeOneCoordinateVector_of_gt hka
      funext j
      simpa [degreeOneFinVector] using (congrFun hfix j).symm
    · have hcases : (a : Nat) = (k : Nat) ∨
          (a : Nat) = (k : Nat) + 1 := by omega
      rcases hcases with hak_eq | hak_succ
      · have ha_eq : a = k := Fin.ext hak_eq
        subst a
        by_cases hk0 : (k : Nat) = 0
        · have hn : 0 < n := by omega
          letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
          have hk_eq : k = (0 : Fin n) := Fin.ext (by simpa using hk0)
          subst k
          have hp : standardLowerEntry hstd T = adjacentEntryHi 0 := by
            apply Fin.ext
            simp [T, adjacentEntryHi, hn]
          have hcol := adjacentSameCol_of_lowerEntry_eq_hi_zero
            hstd T 0 hp (by simp)
          rw [youngAdjacentOperator_basis_sameCol T 0 hcol]
          change standardCoordinateMap hstd (-tableauBasisVec T) = _
          rw [map_neg, standardCoordinateMap_tableauBasisVec_index,
            permutationCoordinateRho_adjacent_degreeOneFinVector]
          have hneg := natAdjacentCoordinateSwap_degreeOneCoordinateVector_zero
          funext j
          simpa [degreeOneFinVector] using (congrFun hneg j).symm
        · have hkpos : 0 < (k : Nat) := by omega
          have hp : standardLowerEntry hstd T = adjacentEntryHi k := by
            apply Fin.ext
            simp [T, adjacentEntryHi]
          have hrow := not_adjacentSameRow_of_lowerEntry_eq_hi hstd T k hp
          have hcol := not_adjacentSameCol_of_lowerEntry_eq_hi_pos
            hstd T k hp hkpos
          let kp : Fin n := ⟨(k : Nat) - 1, by omega⟩
          have hswap : adjacentSwapTableau T k hrow hcol =
              standardTableauOfIndex hstd kp := by
            apply standardYoungTableau_eq_of_lowerEntry_eq hstd
            rw [standardLowerEntry_adjacentSwap_eq_lo_of_eq_hi
              hstd T k hp hrow hcol,
              standardLowerEntry_standardTableauOfIndex]
            apply Fin.ext
            simp [adjacentEntryLo, kp]
            omega
          rw [youngAdjacentOperator_basis_swappable_eq T k hrow hcol]
          change standardCoordinateMap hstd
              (youngAdjacentDiagCoeff T k • tableauBasisVec T +
                youngAdjacentOffCoeff T k •
                  tableauBasisVec (adjacentSwapTableau T k hrow hcol)) = _
          rw [map_add, map_smul, map_smul, hswap,
            standardCoordinateMap_tableauBasisVec_index,
            standardCoordinateMap_tableauBasisVec_index,
            youngAdjacentDiagCoeff_of_lowerEntry_eq_hi hstd T k hp,
            youngAdjacentOffCoeff_of_lowerEntry_eq_hi hstd T k hp,
            permutationCoordinateRho_adjacent_degreeOneFinVector]
          have hleft :=
            natAdjacentCoordinateSwap_degreeOneCoordinateVector_left
              ((k : Nat) - 1)
          have hindex : (kp : Nat) + 1 = (k : Nat) := by simp [kp]; omega
          funext j
          have hj := congrFun hleft j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            degreeOneFinVector]
          simpa [hindex, kp, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc] using hj.symm
      · have ha_val : (a : Nat) = (k : Nat) + 1 := hak_succ
        have hp : standardLowerEntry hstd T = adjacentEntryLo a := by
          apply Fin.ext
          simp [T, adjacentEntryLo, ha_val]
        have hrow := not_adjacentSameRow_of_lowerEntry_eq_lo hstd T a hp
        have hcol := not_adjacentSameCol_of_lowerEntry_eq_lo hstd T a hp
        have hswap : adjacentSwapTableau T a hrow hcol =
            standardTableauOfIndex hstd a := by
          apply standardYoungTableau_eq_of_lowerEntry_eq hstd
          rw [standardLowerEntry_adjacentSwap_eq_hi_of_eq_lo
            hstd T a hp hrow hcol,
            standardLowerEntry_standardTableauOfIndex]
          rfl
        rw [youngAdjacentOperator_basis_swappable_eq T a hrow hcol]
        change standardCoordinateMap hstd
            (youngAdjacentDiagCoeff T a • tableauBasisVec T +
              youngAdjacentOffCoeff T a •
                tableauBasisVec (adjacentSwapTableau T a hrow hcol)) = _
        rw [map_add, map_smul, map_smul, hswap,
          standardCoordinateMap_tableauBasisVec_index,
          standardCoordinateMap_tableauBasisVec_index,
          youngAdjacentDiagCoeff_of_lowerEntry_eq_lo hstd T a hp,
          youngAdjacentOffCoeff_of_lowerEntry_eq_lo hstd T a hp,
          permutationCoordinateRho_adjacent_degreeOneFinVector]
        have hright :=
          natAdjacentCoordinateSwap_degreeOneCoordinateVector_right k
        funext j
        have hj := congrFun hright j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          degreeOneFinVector]
        simpa [ha_val] using hj.symm

/-- The adjacent Young operator as a linear map. -/
noncomputable def youngAdjacentLinearMap {n : Nat}
    {lam : YoungDiagram (n + 1)} (a : Fin n) :
    TableauSpace lam →ₗ[Real] TableauSpace lam where
  toFun := youngAdjacentOperator a
  map_add' := youngAdjacentOperator_add a
  map_smul' := by
    intro c f
    change youngAdjacentOperator a (fun S => c * f S) =
      fun S => c * youngAdjacentOperator a f S
    exact youngAdjacentOperator_smul a c f

/-- A coordinate permutation as a linear map. -/
def permutationCoordinateLinearMap {n : Nat} (pi : Perm (Fin n)) :
    (Fin n → Real) →ₗ[Real] (Fin n → Real) where
  toFun := permutationCoordinateRho pi
  map_add' := by
    intro v w
    rfl
  map_smul' := by
    intro c v
    rfl

/-- The standard-coordinate map intertwines every adjacent generator. -/
theorem standardCoordinateMap_youngAdjacentOperator {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (a : Fin n) (f : TableauSpace lam) :
    standardCoordinateMap hstd (youngAdjacentOperator a f) =
      permutationCoordinateRho (appA_adjacentTransposition a)
        (standardCoordinateMap hstd f) := by
  have hexp : f = ∑ T : StandardYoungTableau lam,
      f T • tableauBasisVec T := by
    funext S
    have hS := congrFun (tableauBasis_expansion f) S
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hS
  let L := (standardCoordinateMap hstd).comp (youngAdjacentLinearMap a)
  let R := (permutationCoordinateLinearMap
      (appA_adjacentTransposition a)).comp (standardCoordinateMap hstd)
  change L f = R f
  rw [hexp, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, map_smul]
  apply congrArg (f T • ·)
  let k := standardTableauIndex hstd T
  have hT : T = standardTableauOfIndex hstd k := by
    change T = standardTableauOfIndex hstd
      (standardTableauIndex hstd T)
    exact (standardTableauOfIndex_tableauIndex hstd T).symm
  rw [hT]
  exact standardCoordinateMap_youngAdjacentOperator_basis hstd a k

/-- The standard-coordinate map intertwines the supplied Young action with
the coordinate permutation representation for every permutation. -/
theorem standardCoordinateMap_intertwines_youngAction {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (action : YoungOrthogonalActionData lam) (pi : Perm (Fin (n + 1)))
    (f : TableauSpace lam) :
    standardCoordinateMap hstd (action.rep.rho pi f) =
      permutationCoordinateRho pi (standardCoordinateMap hstd f) := by
  let M : Submonoid (Perm (Fin (n + 1))) :=
    { carrier := {sigma | ∀ g : TableauSpace lam,
        standardCoordinateMap hstd (action.rep.rho sigma g) =
          permutationCoordinateRho sigma (standardCoordinateMap hstd g)}
      one_mem' := by
        intro g
        rw [action.rep.map_one]
        rfl
      mul_mem' := by
        intro sigma tau hs ht g
        rw [action.rep.map_mul, hs, ht]
        exact ((permutationCoordinateRepresentation (Fin (n + 1))).map_mul
          sigma tau (standardCoordinateMap hstd g)).symm }
  have hgen : Set.range (fun a : Fin n => appA_adjacentTransposition a) ⊆ M := by
    rintro _ ⟨a, rfl⟩ g
    rw [action.rho_adjacent]
    exact standardCoordinateMap_youngAdjacentOperator hstd a g
  have hclosure : Submonoid.closure
      (Set.range (fun a : Fin n => appA_adjacentTransposition a)) ≤ M :=
    Submonoid.closure_le.2 hgen
  have htop : Submonoid.closure
      (Set.range (fun a : Fin n => appA_adjacentTransposition a)) = ⊤ := by
    simpa [appA_adjacentTransposition] using
      Equiv.Perm.mclosure_swap_castSucc_succ n
  have hpi : pi ∈ Submonoid.closure
      (Set.range (fun a : Fin n => appA_adjacentTransposition a)) := by
    rw [htop]
    trivial
  exact hclosure hpi f

/-! ## Coordinate matrix coefficients -/

/-- Expansion in the standard coordinate basis. -/
theorem permutationCoordinateBasis_expansion {n : Nat}
    (v : Fin n → Real) :
    v = ∑ i : Fin n, v i • permutationCoordinateBasisVec i := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single j]
  · simp [permutationCoordinateBasisVec]
  · intro i hij
    simp [permutationCoordinateBasisVec, Ne.symm hij]

/-- A coordinate of a permuted vector is a linear combination of one-coset
indicators. -/
theorem permutationCoordinateRho_eq_sum_oneCosetReal {n : Nat}
    (pi : Perm (Fin n)) (v : Fin n → Real) (j : Fin n) :
    permutationCoordinateRho pi v j =
      ∑ i : Fin n, v i * oneCosetReal i j pi := by
  classical
  rw [Fintype.sum_eq_single (pi.symm j)]
  · simp [permutationCoordinateRho, oneCosetReal]
  · intro i hi
    have hne : pi i ≠ j := by
      intro h
      apply hi
      apply pi.injective
      simp [h]
    simp [oneCosetReal, hne]

/-- Any linear functional applied to a permuted coordinate vector is a finite
linear combination of one-coset indicators, hence belongs to `U1`. -/
theorem coordinateLinearCoefficient_mem_U1 {n : Nat}
    (ell : (Fin n → Real) →ₗ[Real] Real) (v : Fin n → Real) :
    (fun pi : Perm (Fin n) => ell (permutationCoordinateRho pi v)) ∈
      U1 (Fin n) := by
  classical
  have hfun : (fun pi : Perm (Fin n) =>
      ell (permutationCoordinateRho pi v)) =
      ∑ j : Fin n, ∑ i : Fin n,
        (v i * ell (permutationCoordinateBasisVec j)) •
          oneCosetReal i j := by
    funext pi
    have hexp := permutationCoordinateBasis_expansion
      (permutationCoordinateRho pi v)
    have hell := congrArg ell hexp
    simp only [map_sum, map_smul] at hell
    rw [hell]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [permutationCoordinateRho_eq_sum_oneCosetReal]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(i, j), rfl⟩

/-! ## The standard block lies in `U1` -/

/-- Reindex the coordinates of a standard-shape tableau vector by the entry in
its lower box. -/
def standardTableauCoordinates {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam) :
    TableauSpace lam →ₗ[Real] (Fin n → Real) where
  toFun f := fun k => f (standardTableauOfIndex hstd k)
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- The standard-coordinate embedding is the nonconstant summand of the full
triangular coordinate equivalence. -/
theorem standardCoordinateMap_eq_degreeOneCoordinateSynthesis {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (f : TableauSpace lam) :
    standardCoordinateMap hstd f =
      degreeOneCoordinateSynthesis n (0, standardTableauCoordinates hstd f) := by
  funext j
  change (∑ T : StandardYoungTableau lam,
      f T * degreeOneFinVector (standardTableauIndex hstd T) j) =
    0 + ∑ k : Fin n,
      standardTableauCoordinates hstd f k * degreeOneCoordinateVector k j
  rw [← (standardTableauEquivFin hstd).sum_comp
    (fun T : StandardYoungTableau lam =>
      f T * degreeOneFinVector (standardTableauIndex hstd T) j)]
  simp [standardTableauEquivFin, standardTableauCoordinates,
    degreeOneFinVector]

/-- Recover one tableau coordinate from the full permutation-coordinate
space, using the inverse triangular coordinate equivalence. -/
noncomputable def standardCoordinateFunctional {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (S : StandardYoungTableau lam) :
    (Fin (n + 1) → Real) →ₗ[Real] Real where
  toFun w := ((degreeOneCoordinateEquiv n).symm w).2
    (standardTableauIndex hstd S)
  map_add' := by
    intro v w
    simp
  map_smul' := by
    intro c v
    simp

/-- The inverse coordinate functional recovers the original tableau
coefficient. -/
@[simp] theorem standardCoordinateFunctional_standardCoordinateMap {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (S : StandardYoungTableau lam) (f : TableauSpace lam) :
    standardCoordinateFunctional hstd S (standardCoordinateMap hstd f) =
      f S := by
  rw [standardCoordinateMap_eq_degreeOneCoordinateSynthesis]
  change (((degreeOneCoordinateEquiv n).symm
      ((degreeOneCoordinateEquiv n)
        (0, standardTableauCoordinates hstd f))).2
          (standardTableauIndex hstd S)) = f S
  rw [LinearEquiv.symm_apply_apply]
  simp [standardTableauCoordinates]

/-- Every matrix coefficient of a standard `(n,1)` Young action belongs to
the concrete permutation-coordinate coefficient space `U1`. -/
theorem youngMatrixCoefficient_mem_U1_of_isStandard {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (action : YoungOrthogonalActionData lam)
    (S T : StandardYoungTableau lam) :
    youngMatrixCoefficient action S T ∈ U1 (Fin (n + 1)) := by
  let ell := standardCoordinateFunctional hstd S
  let v := standardCoordinateMap hstd (tableauBasisVec T)
  have hmem := coordinateLinearCoefficient_mem_U1 ell v
  have heq : (fun pi : Perm (Fin (n + 1)) =>
      ell (permutationCoordinateRho pi v)) =
      youngMatrixCoefficient action S T := by
    funext pi
    change standardCoordinateFunctional hstd S
        (permutationCoordinateRho pi
          (standardCoordinateMap hstd (tableauBasisVec T))) = _
    rw [← standardCoordinateMap_intertwines_youngAction
      hstd action pi (tableauBasisVec T)]
    rw [standardCoordinateFunctional_standardCoordinateMap]
    simp [youngMatrixCoefficient, tableauInner_left_basis]
  rw [heq] at hmem
  exact hmem

/-- The whole concrete standard Young block is contained in `U1`. -/
theorem youngMatrixCoefficientBlock_le_U1_of_isStandard {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (action : YoungOrthogonalActionData lam) :
    youngMatrixCoefficientBlock action ≤ U1 (Fin (n + 1)) := by
  apply Submodule.span_le.2
  rintro F ⟨ST, rfl⟩
  exact youngMatrixCoefficient_mem_U1_of_isStandard
    hstd action ST.1 ST.2

/-! ## The one-row block is the constant line -/

/-- Every positive-indexed row of a one-row diagram is empty. -/
theorem youngRow_eq_zero_of_isOneRow_of_pos {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    {r : Nat} (hr : 0 < r) :
    youngRow lam r = 0 := by
  classical
  by_cases hrn : r < n + 1
  · let i0 : Fin (n + 1) := ⟨0, by omega⟩
    let ir : Fin (n + 1) := ⟨r, hrn⟩
    let tail := (Finset.univ : Finset (Fin (n + 1))).erase i0
    have hir : ir ∈ tail := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ ir⟩
      intro h
      have hv := congrArg Fin.val h
      simp [ir, i0] at hv
      omega
    have hsum :
        (lam.row i0 : Nat) +
            tail.sum (fun i => (lam.row i : Nat)) = n + 1 := by
      simpa [tail, add_comm] using
        (Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
          (fun i => (lam.row i : Nat)) (Finset.mem_univ i0)).trans
          lam.sum_rows
    have hrow0 : (lam.row i0 : Nat) = n + 1 := by
      simpa [IsOneRow, youngRow, i0] using hrow
    have htail : tail.sum (fun i => (lam.row i : Nat)) = 0 := by
      omega
    have hir_le : (lam.row ir : Nat) ≤
        tail.sum (fun i => (lam.row i : Nat)) :=
      Finset.single_le_sum
        (fun i _ => Nat.zero_le (lam.row i : Nat)) hir
    have hz : (lam.row ir : Nat) = 0 := by omega
    simpa [youngRow, hrn, ir] using hz
  · simp [youngRow, hrn]

/-- Every cell of a one-row diagram lies in row zero. -/
theorem youngCell_row_eq_zero_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (u : YoungCell lam) :
    YoungCell.row u = 0 := by
  by_contra hne
  have hr : 0 < YoungCell.row u := by omega
  have hz := youngRow_eq_zero_of_isOneRow_of_pos hrow hr
  have hbox := YoungCell.isYoungBox u
  change YoungCell.col u < youngRow lam (YoungCell.row u) at hbox
  rw [hz] at hbox
  omega

/-- The row-reading tableau of a one-row diagram. -/
noncomputable def oneRowStandardTableau {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam) :
    StandardYoungTableau lam where
  entry := fun u => u.1.2
  bijective := by
    constructor
    · intro u v huv
      apply YoungCell.ext_row_col
      · rw [youngCell_row_eq_zero_of_isOneRow hrow,
          youngCell_row_eq_zero_of_isOneRow hrow]
      · exact congrArg Fin.val huv
    · intro j
      let u := youngCellOfNat lam 0 (j : Nat) (by
        rw [hrow]
        exact j.isLt)
      refine ⟨u, ?_⟩
      apply Fin.ext
      simp [u, youngCellOfNat]
  row_strict := by
    intro u v _hrows hcols
    exact hcols
  col_strict := by
    intro u v _hcols hrows
    rw [youngCell_row_eq_zero_of_isOneRow hrow,
      youngCell_row_eq_zero_of_isOneRow hrow] at hrows
    omega

/-- Every adjacent pair in a one-row tableau occupies the same row. -/
theorem adjacentSameRow_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (T : StandardYoungTableau lam) (a : Fin n) :
    adjacentSameRow T a := by
  unfold adjacentSameRow
  rw [youngCell_row_eq_zero_of_isOneRow hrow,
    youngCell_row_eq_zero_of_isOneRow hrow]

/-- A supplied Young action fixes every tableau basis vector of a one-row
shape. -/
theorem youngAction_fix_tableauBasis_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam)
    (pi : Perm (Fin (n + 1))) (T : StandardYoungTableau lam) :
    action.rep.rho pi (tableauBasisVec T) = tableauBasisVec T := by
  let M : Submonoid (Perm (Fin (n + 1))) :=
    { carrier := {sigma |
        action.rep.rho sigma (tableauBasisVec T) = tableauBasisVec T}
      one_mem' := action.rep.map_one (tableauBasisVec T)
      mul_mem' := by
        intro sigma tau hs ht
        change action.rep.rho (sigma * tau) (tableauBasisVec T) =
          tableauBasisVec T
        change action.rep.rho sigma (tableauBasisVec T) =
          tableauBasisVec T at hs
        change action.rep.rho tau (tableauBasisVec T) =
          tableauBasisVec T at ht
        rw [action.rep.map_mul, ht, hs] }
  have hgen : Set.range (fun a : Fin n => appA_adjacentTransposition a) ⊆ M := by
    rintro _ ⟨a, rfl⟩
    change action.rep.rho (appA_adjacentTransposition a)
      (tableauBasisVec T) = tableauBasisVec T
    rw [action.rho_adjacent]
    exact youngAdjacentOperator_basis_sameRow T a
      (adjacentSameRow_of_isOneRow hrow T a)
  have hclosure : Submonoid.closure
      (Set.range (fun a : Fin n => appA_adjacentTransposition a)) ≤ M :=
    Submonoid.closure_le.2 hgen
  have htop : Submonoid.closure
      (Set.range (fun a : Fin n => appA_adjacentTransposition a)) = ⊤ := by
    simpa [appA_adjacentTransposition] using
      Equiv.Perm.mclosure_swap_castSucc_succ n
  apply hclosure
  rw [htop]
  trivial

/-- The constant-one function on a permutation group. -/
def permutationConstantOne (α : Type*) : Perm α → Real :=
  fun _ => 1

/-- A diagonal one-row matrix coefficient is the constant-one function. -/
theorem youngMatrixCoefficient_self_eq_constant_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam)
    (T : StandardYoungTableau lam) :
    youngMatrixCoefficient action T T =
      permutationConstantOne (Fin (n + 1)) := by
  funext pi
  rw [youngMatrixCoefficient,
    youngAction_fix_tableauBasis_of_isOneRow hrow action pi T]
  simp [permutationConstantOne]

/-- An off-diagonal one-row matrix coefficient is zero. -/
theorem youngMatrixCoefficient_eq_zero_of_isOneRow_of_ne {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam)
    {S T : StandardYoungTableau lam} (hST : S ≠ T) :
    youngMatrixCoefficient action S T = 0 := by
  funext pi
  rw [youngMatrixCoefficient,
    youngAction_fix_tableauBasis_of_isOneRow hrow action pi T]
  exact tableauInner_basis_basis_ne hST

/-- Summing one row of permutation matrix coefficients gives the constant-one
function. -/
theorem permutationConstantOne_eq_sum_oneCosetReal
    {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    permutationConstantOne α = ∑ j : α, oneCosetReal i j := by
  funext pi
  simp only [permutationConstantOne, Finset.sum_apply]
  rw [Fintype.sum_eq_single (pi i)]
  · simp [oneCosetReal]
  · intro j hji
    simp [oneCosetReal, Ne.symm hji]

/-- The constant-one function belongs to `U1` on every nonempty finite set. -/
theorem permutationConstantOne_mem_U1
    {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    permutationConstantOne α ∈ U1 α := by
  rw [permutationConstantOne_eq_sum_oneCosetReal i]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.subset_span ⟨(i, j), rfl⟩

/-- Every matrix coefficient of a one-row Young action belongs to `U1`. -/
theorem youngMatrixCoefficient_mem_U1_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam)
    (S T : StandardYoungTableau lam) :
    youngMatrixCoefficient action S T ∈ U1 (Fin (n + 1)) := by
  by_cases hST : S = T
  · subst T
    rw [youngMatrixCoefficient_self_eq_constant_of_isOneRow hrow]
    exact permutationConstantOne_mem_U1 (0 : Fin (n + 1))
  · rw [youngMatrixCoefficient_eq_zero_of_isOneRow_of_ne hrow action hST]
    exact Submodule.zero_mem _

/-- The whole concrete one-row Young block is contained in `U1`. -/
theorem youngMatrixCoefficientBlock_le_U1_of_isOneRow {n : Nat}
    {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam) :
    youngMatrixCoefficientBlock action ≤ U1 (Fin (n + 1)) := by
  apply Submodule.span_le.2
  rintro F ⟨ST, rfl⟩
  exact youngMatrixCoefficient_mem_U1_of_isOneRow
    hrow action ST.1 ST.2

/-- The constant-one function lies in every concrete one-row Young block. -/
theorem permutationConstantOne_mem_youngMatrixCoefficientBlock_of_isOneRow
    {n : Nat} {lam : YoungDiagram (n + 1)} (hrow : IsOneRow lam)
    (action : YoungOrthogonalActionData lam) :
    permutationConstantOne (Fin (n + 1)) ∈
    youngMatrixCoefficientBlock action := by
  classical
  let T := oneRowStandardTableau hrow
  have hgen : youngMatrixCoefficient action T T ∈
      youngMatrixCoefficientBlock action :=
    Submodule.subset_span ⟨(T, T), rfl⟩
  rwa [youngMatrixCoefficient_self_eq_constant_of_isOneRow hrow] at hgen

/-! ## The faithful degree-one block equality -/

/-- The concrete sum of all one-row and standard blocks is contained in
`U1`. -/
theorem concreteDegreeOneYoungBlockSum_le_U1 {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam) :
    concreteDegreeOneYoungBlockSum action ≤ U1 (Fin (n + 1)) := by
  unfold concreteDegreeOneYoungBlockSum
  refine iSup_le fun lam => ?_
  refine iSup_le fun hlam => ?_
  rcases hlam with hrow | hstd
  · exact youngMatrixCoefficientBlock_le_U1_of_isOneRow
      hrow (action lam)
  · exact youngMatrixCoefficientBlock_le_U1_of_isStandard
      hstd (action lam)

/-- The canonical one-row diagram satisfies the one-row predicate. -/
theorem isOneRow_oneRowDiagram_degreeOne (N : Nat) :
    IsOneRow (oneRowDiagram N) := by
  by_cases hN : N = 0
  · subst N
    rfl
  · simp [IsOneRow, oneRowDiagram, youngRow, hN]

/-- The canonical standard diagram of size `n+1`, for `n > 0`. -/
def degreeOneStandardDiagram (n : Nat) (hn : 0 < n) :
    YoungDiagram (n + 1) :=
  twoRowDiagram (n + 1) n 1 (by omega) (by omega) (by omega)

/-- The canonical two-row diagram has standard shape `(n,1)`. -/
theorem isStandard_degreeOneStandardDiagram (n : Nat) (hn : 0 < n) :
    IsStandard (degreeOneStandardDiagram n hn) := by
  unfold degreeOneStandardDiagram IsStandard
  simp [twoRowDiagram, youngRow, hn]
  omega

/-- Expand one coordinate of the orbit of an arbitrary tableau vector in the
matrix-coefficient basis. -/
theorem youngAction_apply_eq_sum_youngMatrixCoefficient {n : Nat}
    {lam : YoungDiagram (n + 1)}
    (action : YoungOrthogonalActionData lam)
    (pi : Perm (Fin (n + 1))) (f : TableauSpace lam)
    (S : StandardYoungTableau lam) :
    action.rep.rho pi f S =
      ∑ T : StandardYoungTableau lam,
        f T * youngMatrixCoefficient action S T pi := by
  classical
  have hf : f = ∑ T : StandardYoungTableau lam,
      f T • tableauBasisVec T := by
    funext U
    have hU := congrFun (tableauBasis_expansion f) U
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hU
  calc
    action.rep.rho pi f S =
        action.rep.rho pi
          (∑ T : StandardYoungTableau lam,
            f T • tableauBasisVec T) S :=
      congrArg (fun g : TableauSpace lam => action.rep.rho pi g S) hf
    _ = (∑ T : StandardYoungTableau lam,
          action.rep.rho pi (f T • tableauBasisVec T)) S := by
      apply congrArg (fun g : TableauSpace lam => g S)
      exact map_sum (action.rep.linearMap pi)
        (fun T : StandardYoungTableau lam =>
          f T • tableauBasisVec T) Finset.univ
    _ = ∑ T : StandardYoungTableau lam,
          f T * youngMatrixCoefficient action S T pi := by
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro T _
      rw [action.rep.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [youngMatrixCoefficient, tableauInner_left_basis]

/-- A coordinate evaluation of a standard-shape orbit is an explicit
synthesis of concrete Young matrix coefficients. -/
theorem standardCoordinateOrbitEvaluation_eq_youngBlockSynthesis {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (action : YoungOrthogonalActionData lam)
    (f : TableauSpace lam) (j : Fin (n + 1)) :
    (fun pi : Perm (Fin (n + 1)) =>
      standardCoordinateMap hstd (action.rep.rho pi f) j) =
      youngBlockSynthesis action (fun ST =>
        f ST.2 *
          degreeOneFinVector (standardTableauIndex hstd ST.1) j) := by
  classical
  funext pi
  change (∑ S : StandardYoungTableau lam,
      action.rep.rho pi f S *
        degreeOneFinVector (standardTableauIndex hstd S) j) =
    ∑ ST : StandardYoungTableau lam × StandardYoungTableau lam,
      (f ST.2 *
          degreeOneFinVector (standardTableauIndex hstd ST.1) j) *
        youngMatrixCoefficient action ST.1 ST.2 pi
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro S _
  rw [youngAction_apply_eq_sum_youngMatrixCoefficient]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  ring

/-- A coordinate evaluation of a standard-shape orbit belongs to its concrete
Young block. -/
theorem standardCoordinateOrbitEvaluation_mem_youngMatrixCoefficientBlock
    {n : Nat} {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (action : YoungOrthogonalActionData lam)
    (f : TableauSpace lam) (j : Fin (n + 1)) :
    (fun pi : Perm (Fin (n + 1)) =>
      standardCoordinateMap hstd (action.rep.rho pi f) j) ∈
      youngMatrixCoefficientBlock action := by
  rw [standardCoordinateOrbitEvaluation_eq_youngBlockSynthesis]
  exact youngBlockSynthesis_mem_youngMatrixCoefficientBlock _ _

/-- Turn coordinates indexed by `Fin n` back into a vector on the standard
tableaux of any standard shape. -/
def standardTableauVectorOfCoordinates {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (g : Fin n → Real) : TableauSpace lam :=
  fun T => g (standardTableauIndex hstd T)

@[simp] theorem standardTableauCoordinates_vectorOfCoordinates {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (g : Fin n → Real) :
    standardTableauCoordinates hstd
      (standardTableauVectorOfCoordinates hstd g) = g := by
  funext k
  simp [standardTableauCoordinates, standardTableauVectorOfCoordinates]

/-- The standard-coordinate embedding of reconstructed tableau coordinates is
exactly the nonconstant triangular summand. -/
theorem standardCoordinateMap_vectorOfCoordinates {n : Nat}
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (g : Fin n → Real) :
    standardCoordinateMap hstd
        (standardTableauVectorOfCoordinates hstd g) =
      degreeOneCoordinateSynthesis n (0, g) := by
  rw [standardCoordinateMap_eq_degreeOneCoordinateSynthesis]
  rw [standardTableauCoordinates_vectorOfCoordinates]

/-- The triangular synthesis splits into its constant and standard
summands. -/
theorem degreeOneCoordinateSynthesis_split (n : Nat)
    (c : Real) (g : Fin n → Real) :
    degreeOneCoordinateSynthesis n (c, g) =
      (fun _ => c) + degreeOneCoordinateSynthesis n (0, g) := by
  funext j
  change c + ∑ k : Fin n, g k * degreeOneCoordinateVector k j =
    c + (0 + ∑ k : Fin n, g k * degreeOneCoordinateVector k j)
  ring

/-- A permuted coordinate basis vector evaluates to the corresponding
one-coset indicator. -/
theorem permutationCoordinateRho_basis_eq_oneCosetReal {n : Nat}
    (pi : Perm (Fin n)) (i j : Fin n) :
    permutationCoordinateRho pi (permutationCoordinateBasisVec i) j =
      oneCosetReal i j pi := by
  rw [permutationCoordinateRho_eq_sum_oneCosetReal]
  rw [Fintype.sum_eq_single i]
  · simp [permutationCoordinateBasisVec]
  · intro k hki
    simp [permutationCoordinateBasisVec, hki]

/-- In rank one every one-coset indicator is the constant-one function. -/
theorem oneCosetReal_fin_one_eq_constant (i j : Fin 1) :
    oneCosetReal i j = permutationConstantOne (Fin 1) := by
  funext pi
  have hij : pi i = j := Subsingleton.elim _ _
  simp [oneCosetReal, permutationConstantOne, hij]

/-- The constant line is contained in the concrete degree-one Young-block
sum. -/
theorem permutationConstantOne_mem_concreteDegreeOneYoungBlockSum {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam) :
    permutationConstantOne (Fin (n + 1)) ∈
      concreteDegreeOneYoungBlockSum action := by
  let lam := oneRowDiagram (n + 1)
  have hrow : IsOneRow lam :=
    isOneRow_oneRowDiagram_degreeOne (n + 1)
  apply youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
    action lam (Or.inl hrow)
  exact
    permutationConstantOne_mem_youngMatrixCoefficientBlock_of_isOneRow
      hrow (action lam)

/-- Every coordinate evaluation of a standard-shape orbit belongs to the
concrete degree-one Young-block sum. -/
theorem standardCoordinateOrbitEvaluation_mem_concreteDegreeOneYoungBlockSum
    {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam)
    {lam : YoungDiagram (n + 1)} (hstd : IsStandard lam)
    (f : TableauSpace lam) (j : Fin (n + 1)) :
    (fun pi : Perm (Fin (n + 1)) =>
      standardCoordinateMap hstd ((action lam).rep.rho pi f) j) ∈
      concreteDegreeOneYoungBlockSum action := by
  apply youngMatrixCoefficientBlock_le_concreteDegreeOneYoungBlockSum
    action lam (Or.inr hstd)
  exact standardCoordinateOrbitEvaluation_mem_youngMatrixCoefficientBlock
    hstd (action lam) f j

/-- Every one-coset generator belongs to the sum of the concrete one-row and
standard Young blocks. -/
theorem oneCosetReal_mem_concreteDegreeOneYoungBlockSum {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam)
    (i j : Fin (n + 1)) :
    oneCosetReal i j ∈ concreteDegreeOneYoungBlockSum action := by
  by_cases hn : n = 0
  · subst n
    rw [oneCosetReal_fin_one_eq_constant]
    exact permutationConstantOne_mem_concreteDegreeOneYoungBlockSum action
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let lam := degreeOneStandardDiagram n hnpos
    let hstd : IsStandard lam :=
      isStandard_degreeOneStandardDiagram n hnpos
    let e : Fin (n + 1) → Real := permutationCoordinateBasisVec i
    let x : Real × (Fin n → Real) :=
      (degreeOneCoordinateEquiv n).symm e
    let f : TableauSpace lam :=
      standardTableauVectorOfCoordinates hstd x.2
    have hx : degreeOneCoordinateSynthesis n x = e := by
      change (degreeOneCoordinateEquiv n) x = e
      exact LinearEquiv.apply_symm_apply (degreeOneCoordinateEquiv n) e
    have hf : standardCoordinateMap hstd f =
        degreeOneCoordinateSynthesis n (0, x.2) := by
      exact standardCoordinateMap_vectorOfCoordinates hstd x.2
    have hsplit : e =
        (fun _ => x.1) + standardCoordinateMap hstd f := by
      calc
        e = degreeOneCoordinateSynthesis n x := hx.symm
        _ = (fun _ => x.1) +
            degreeOneCoordinateSynthesis n (0, x.2) :=
          degreeOneCoordinateSynthesis_split n x.1 x.2
        _ = (fun _ => x.1) + standardCoordinateMap hstd f := by
          rw [hf]
    have hdecomp : oneCosetReal i j =
        x.1 • permutationConstantOne (Fin (n + 1)) +
          (fun pi : Perm (Fin (n + 1)) =>
            standardCoordinateMap hstd ((action lam).rep.rho pi f) j) := by
      funext pi
      rw [← permutationCoordinateRho_basis_eq_oneCosetReal]
      change permutationCoordinateRho pi e j = _
      rw [hsplit]
      simp only [permutationCoordinateRho, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, permutationConstantOne]
      rw [standardCoordinateMap_intertwines_youngAction
        hstd (action lam) pi f]
      simp [permutationCoordinateRho]
    have hconst : permutationConstantOne (Fin (n + 1)) ∈
        concreteDegreeOneYoungBlockSum action :=
      permutationConstantOne_mem_concreteDegreeOneYoungBlockSum action
    have hstandard :
        (fun pi : Perm (Fin (n + 1)) =>
          standardCoordinateMap hstd ((action lam).rep.rho pi f) j) ∈
          concreteDegreeOneYoungBlockSum action :=
      standardCoordinateOrbitEvaluation_mem_concreteDegreeOneYoungBlockSum
        action hstd f j
    have hsum :
        x.1 • permutationConstantOne (Fin (n + 1)) +
            (fun pi : Perm (Fin (n + 1)) =>
              standardCoordinateMap hstd ((action lam).rep.rho pi f) j) ∈
          concreteDegreeOneYoungBlockSum action :=
      Submodule.add_mem _ (Submodule.smul_mem _ x.1 hconst) hstandard
    rwa [← hdecomp] at hsum

/-- `U1` is contained in the concrete sum of the one-row and standard Young
blocks. -/
theorem U1_le_concreteDegreeOneYoungBlockSum {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) ≤ concreteDegreeOneYoungBlockSum action := by
  unfold U1
  apply Submodule.span_le.2
  rintro F ⟨ij, rfl⟩
  exact oneCosetReal_mem_concreteDegreeOneYoungBlockSum
    action ij.1 ij.2

/-- Faithful Appendix A.3: the degree-one permutation-coordinate coefficient
space is exactly the sum of the concrete one-row and standard Young blocks. -/
theorem U1_eq_concreteDegreeOneYoungBlockSum {n : Nat}
    (action : ∀ lam : YoungDiagram (n + 1),
      YoungOrthogonalActionData lam) :
    U1 (Fin (n + 1)) = concreteDegreeOneYoungBlockSum action := by
  apply le_antisymm
  · exact U1_le_concreteDegreeOneYoungBlockSum action
  · exact concreteDegreeOneYoungBlockSum_le_U1 action

end DictatorshipTesting
