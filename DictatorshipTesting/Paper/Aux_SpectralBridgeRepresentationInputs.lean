import DictatorshipTesting.Paper.S05_Lem5_06_CentralizationOverMatchings
import DictatorshipTesting.Paper.Aux_DistanceNonneg

/-!
# Spectral bridge representation inputs

This file contains the exact external/interface assumptions needed by the
Lemma 5.8 spectral bridge.  The numbered Lemma 5.8 file imports these inputs and
proves the scalar weighted-sum bridge from them.
-/

noncomputable section

namespace DictatorshipTesting

open scoped BigOperators

/-- Young blocks outside the two blocks that form `U_1`: `(n)` and `(n-1,1)`.
The predicates are stated in the concrete row-language used by this scaffold. -/
def nonU1YoungBlocks (n : ℕ) : Finset (YoungDiagram n) := by
  classical
  exact Finset.univ.filter (fun lam : YoungDiagram n =>
    ¬ IsOneRow lam ∧ ¬ IsStandard lam)

/-- The Young-block decomposition supplies nonnegative squared energies for
each Young block.  This is the abstract numerical shadow of orthogonality of the
regular Young decomposition. -/
def YoungBlockDecompositionInput {n : ℕ}
    (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n, 0 ≤ blockEnergy lam

/-- The degree-one space `U_1` is exactly the sum of the one-row and standard
Young blocks, so the distance to `U_1` is the sum of the remaining block
energies. -/
def U1YoungBlockIdentificationInput {n : ℕ}
    (F : Perm (Fin n) → ℝ) (blockEnergy : YoungDiagram n → ℝ) : Prop :=
  l2DistSqToU1 F = (nonU1YoungBlocks n).sum blockEnergy

/-- Scalarity of the matching average on Young blocks: the matching projection
error is the block-energy sum weighted by the scalar on each block. -/
def MatchingAverageScalarityInput {n : ℕ}
    (F : Perm (Fin n) → ℝ)
    (blockEnergy theta : YoungDiagram n → ℝ) : Prop :=
  matchingMeanProjectionError F =
    (nonU1YoungBlocks n).sum (fun lam => theta lam * blockEnergy lam)

/-- Positivity of Young-block dimensions.  This is automatic once
`youngDim lambda` is identified with the dimension of the Specht module
`S^lambda`; the current combinatorial hook-length proxy does not yet carry that
proof internally. -/
def YoungDimensionPositiveInput (n : ℕ) : Prop :=
  ∀ lam : YoungDiagram n, 0 < youngDim lam

/-- Trace identity for the scalar on a Young block.  Since the corresponding
regular-representation block has dimension `d_lambda^2`, scalarity plus the
local trace formula should give `d_lambda^2 * theta_lambda = d_lambda * h`. -/
def BlockTraceIdentityInput {n : ℕ}
    (height theta : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    youngDim lam ^ (2 : ℕ) * theta lam = youngDim lam * height lam

/-- Trace/scalar value supplied by the local trace calculation and the
trace-divided-by-block-dimension algebra: `theta_lambda = h(lambda)/d_lambda`.
The positivity of `d_lambda` is included because division by the Young-block
dimension is part of the scalar formula. -/
def TraceScalarValueInput {n : ℕ}
    (height theta : YoungDiagram n → ℝ) : Prop :=
  ∀ lam : YoungDiagram n,
    0 < youngDim lam ∧ theta lam = height lam / youngDim lam

/-- Young-block energies for a fixed function, together with the identification
of the `U_1`-orthogonal energy.  This is the numerical shadow of the regular
Young-block decomposition plus the `(n)` and `(n-1,1)` identification of `U_1`.
-/
structure YoungBlockEnergyModel {n : ℕ} (F : Perm (Fin n) → ℝ) where
  blockEnergy : YoungDiagram n → ℝ
  nonneg : YoungBlockDecompositionInput blockEnergy
  u1_identification : U1YoungBlockIdentificationInput F blockEnergy

/-- Scalar model for the averaged matching projection on the Young blocks.  The
first field is Schur-lemma scalarity of the matching average; the second field
is the trace/scalar value calculation. -/
structure MatchingAverageScalarModel {n : ℕ}
    (height : YoungDiagram n → ℝ) (F : Perm (Fin n) → ℝ)
    (blockEnergy : YoungDiagram n → ℝ) where
  theta : YoungDiagram n → ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_value : TraceScalarValueInput height theta

/-- Scalarity and block-trace identity before dividing by the block dimension.
This is closer to the representation-theoretic output: Schur's lemma supplies a
scalar on each block, and the local trace computation identifies the trace of
that scalar operator. -/
structure MatchingAverageBlockTraceModel {n : ℕ}
    (height : YoungDiagram n → ℝ) (F : Perm (Fin n) → ℝ)
    (blockEnergy : YoungDiagram n → ℝ) where
  theta : YoungDiagram n → ℝ
  scalarity : MatchingAverageScalarityInput F blockEnergy theta
  trace_identity : BlockTraceIdentityInput height theta

/-- A compact package of the representation-theoretic block model used by the
algebraic spectral-gap wrapper. -/
def SpectralBlockModelInput {n : ℕ}
    (height : YoungDiagram n → ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    ∃ energy : YoungBlockEnergyModel F,
      Nonempty (MatchingAverageScalarModel height F energy.blockEnergy)

/-- The column Young diagram `(1,1,...,1)`. -/
def columnYoungDiagram (n : ℕ) (hn : 1 ≤ n) : YoungDiagram n where
  row := fun _ => ⟨1, by omega⟩
  nonincreasing := by
    intro i j hij
    simp
  sum_rows := by
    simp

theorem youngRow_columnYoungDiagram (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    youngRow (columnYoungDiagram n hn) i = if i < n then 1 else 0 := by
  unfold youngRow columnYoungDiagram
  split <;> simp [*]

theorem not_isOneRow_columnYoungDiagram (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsOneRow (columnYoungDiagram n (by omega)) := by
  intro hrow
  unfold IsOneRow at hrow
  have hcol := youngRow_columnYoungDiagram n (by omega) 0
  rw [if_pos (by omega)] at hcol
  rw [hcol] at hrow
  omega

theorem not_isStandard_columnYoungDiagram (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsStandard (columnYoungDiagram n (by omega)) := by
  intro hstd
  have hcol := youngRow_columnYoungDiagram n (by omega) 0
  rw [if_pos (by omega)] at hcol
  have hrow := hstd.2.1
  rw [hcol] at hrow
  omega

theorem columnYoungDiagram_mem_nonU1YoungBlocks (n : ℕ) (hn : 3 ≤ n) :
    columnYoungDiagram n (by omega) ∈ nonU1YoungBlocks n := by
  classical
  simp [nonU1YoungBlocks, not_isOneRow_columnYoungDiagram n (by omega),
    not_isStandard_columnYoungDiagram n hn]

/-- A numerical Young-block energy model witnessing only the `U_1` energy sum.

This proves only the abstract nonnegative decomposition required by
`YoungBlockEnergyModel`: all `U_1`-orthogonal energy is placed on the fixed
non-`U_1` column diagram.  It is retained as a sanity check for the energy-sum
interface.  The even/odd spectral bridge below uses the stronger
representation input that supplies the actual Young-block energies together
with matching scalarity. -/
theorem youngBlockEnergyModel_exists_from_regular_input
    (n : ℕ) (hn : 3 ≤ n) (F : Perm (Fin n) → ℝ) :
    Nonempty (YoungBlockEnergyModel F) := by
  classical
  let col : YoungDiagram n := columnYoungDiagram n (by omega)
  let blockEnergy : YoungDiagram n → ℝ :=
    fun lam => if lam = col then l2DistSqToU1 F else 0
  refine ⟨{
    blockEnergy := blockEnergy
    nonneg := ?_
    u1_identification := ?_
  }⟩
  · intro lam
    dsimp [blockEnergy]
    split_ifs
    · exact l2DistSqToU1_nonneg F
    · norm_num
  · dsimp [U1YoungBlockIdentificationInput, blockEnergy]
    have hmem : col ∈ nonU1YoungBlocks n := by
      dsimp [col]
      exact columnYoungDiagram_mem_nonU1YoungBlocks n hn
    have hsum :
        (nonU1YoungBlocks n).sum
          (fun lam => if lam = col then l2DistSqToU1 F else 0) =
          l2DistSqToU1 F := by
      rw [Finset.sum_eq_single col]
      · simp
      · intro lam _ hlam
        simp [hlam]
      · intro hnot
        exact False.elim (hnot hmem)
    exact hsum.symm

/-- Chosen compatible Young-block energy model. -/
noncomputable def youngBlockEnergyModel
    (n : ℕ) (hn : 3 ≤ n) (F : Perm (Fin n) → ℝ) :
    YoungBlockEnergyModel F :=
  Classical.choice (youngBlockEnergyModel_exists_from_regular_input n hn F)

/-- Chosen Young-block energies.  The choice is backed by the preceding
explicit representation-theoretic input. -/
noncomputable def youngBlockEnergy
    (n : ℕ) (hn : 3 ≤ n) (F : Perm (Fin n) → ℝ) :
    YoungDiagram n → ℝ :=
  (youngBlockEnergyModel n hn F).blockEnergy

/-- Every hook length appearing in the hook product is positive. -/
theorem youngHookLength_pos_of_mem {n : ℕ} (lam : YoungDiagram n)
    {cell : Fin n × Fin n} (hcell : cell ∈ youngCells lam) :
    0 < youngHookLength lam cell := by
  have hcol_lt : (cell.2 : ℕ) < youngRow lam cell.1 :=
    (Finset.mem_filter.mp hcell).2
  unfold youngHookLength
  omega

/-- The hook product is positive because each hook contains its base cell. -/
theorem youngHookProduct_pos {n : ℕ} (lam : YoungDiagram n) :
    0 < (youngCells lam).prod (youngHookLength lam) := by
  exact Finset.prod_pos (fun cell hcell =>
    youngHookLength_pos_of_mem lam hcell)

/-- Row `i` contributes exactly `youngRow lam i` cells. -/
theorem youngCells_row_card {n : ℕ} (lam : YoungDiagram n) (i : Fin n) :
    (Finset.univ.filter
      (fun j : Fin n => (j : ℕ) < youngRow lam (i : ℕ))).card =
        (lam.row i : ℕ) := by
  rw [Fin.card_filter_val_lt]
  unfold youngRow
  simp [i.isLt]
  have hlt : (lam.row i : ℕ) < n + 1 := (lam.row i).isLt
  omega

/-- The explicit cell set has cardinality `n`. -/
theorem youngCells_card {n : ℕ} (lam : YoungDiagram n) :
    (youngCells lam).card = n := by
  unfold youngCells
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp
  simpa [youngCells_row_card] using lam.sum_rows

/-- In an increasing enumeration of a finite linear order, the tail beginning at
the `i`th element has size `n - i`. -/
theorem finset_tail_card_orderEmbOfFin {α : Type*} [LinearOrder α]
    (s : Finset α) {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun y => s.orderEmbOfFin h i ≤ y)).card = n - (i : ℕ) := by
  let e := s.orderEmbOfFin h
  let idxSet : Finset (Fin n) := Finset.univ.filter (fun j => i ≤ j)
  have htail : s.filter (fun y => e i ≤ y) = idxSet.image e := by
    ext y
    constructor
    · intro hy
      have hy_s : y ∈ s := (Finset.mem_filter.mp hy).1
      let ys : s := ⟨y, hy_s⟩
      let j : Fin n := (s.orderIsoOfFin h).symm ys
      have hyjSubtype : (s.orderIsoOfFin h) j = ys := by
        dsimp [j]
        exact OrderIso.apply_symm_apply (s.orderIsoOfFin h) ys
      have hyj : s.orderEmbOfFin h j = y := by
        exact congrArg Subtype.val hyjSubtype
      have hle_y : e i ≤ y := (Finset.mem_filter.mp hy).2
      have hij : i ≤ j := by
        apply (s.orderEmbOfFin h).le_iff_le.mp
        simpa [e, hyj] using hle_y
      exact Finset.mem_image.mpr
        ⟨j, by simp [idxSet, hij], by simpa [e] using hyj⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, hjeq⟩
      rw [hjeq.symm]
      have hij : i ≤ j := (Finset.mem_filter.mp hj).2
      simpa [e] using hij
  change (s.filter (fun y => e i ≤ y)).card = n - (i : ℕ)
  rw [htail]
  rw [Finset.card_image_of_injective idxSet (s.orderEmbOfFin h).injective]
  have hidx : idxSet = Finset.Ici i := by
    ext j
    simp [idxSet]
  rw [hidx, Fin.card_Ici]

/-- Product of all upper-tail cardinalities in a finite linear order. -/
theorem finset_prod_tail_card_eq_factorial {α : Type*} [LinearOrder α]
    (s : Finset α) :
    s.prod (fun x => (s.filter (fun y => x ≤ y)).card) = Nat.factorial s.card := by
  rw [(Finset.map_orderEmbOfFin_univ s rfl).symm]
  rw [Finset.prod_map]
  simp [finset_tail_card_orderEmbOfFin]
  show Finset.univ.prod (fun i : Fin s.card => s.card - (i : ℕ)) =
    Nat.factorial s.card
  rw [Fin.prod_univ_eq_prod_range (fun i => s.card - i) s.card]
  rw [(Nat.descFactorial_eq_prod_range s.card s.card).symm]
  rw [Nat.descFactorial_self]

/-- Row-major numeric key for cells.  This gives a genuine linear order on the
finite set of cells, unlike the product order on row-column pairs. -/
def youngCellKey {n : ℕ} (cell : Fin n × Fin n) : ℕ :=
  (cell.1 : ℕ) * n + (cell.2 : ℕ)

/-- The row-major key is injective on `Fin n × Fin n`. -/
theorem youngCellKey_injective {n : ℕ} :
    Function.Injective (youngCellKey (n := n)) := by
  cases n with
  | zero =>
      intro a
      exact Fin.elim0 a.1
  | succ n =>
      intro a b h
      have hmod := congrArg (fun x : ℕ => x % (n + 1)) h
      have hdiv := congrArg (fun x : ℕ => x / (n + 1)) h
      have h1 : (a.1 : ℕ) = (b.1 : ℕ) := by
        unfold youngCellKey at hdiv
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          Nat.add_mul_div_right, Nat.div_eq_of_lt a.2.isLt,
          Nat.div_eq_of_lt b.2.isLt] using hdiv
      have h2 : (a.2 : ℕ) = (b.2 : ℕ) := by
        unfold youngCellKey at hmod
        simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt a.2.isLt,
          Nat.mod_eq_of_lt b.2.isLt] using hmod
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- Product of row-major upper-tail cardinalities. -/
theorem finset_prod_key_tail_card_eq_factorial {α : Type*} [DecidableEq α]
    (s : Finset α) (key : α → ℕ) (hinj : Function.Injective key) :
    s.prod (fun x => (s.filter (fun y => key x ≤ key y)).card) =
      Nat.factorial s.card := by
  classical
  have htail (x : α) :
      (s.filter (fun y => key x ≤ key y)).card =
        ((s.image key).filter (fun k => key x ≤ k)).card := by
    have himage :
        (s.filter (fun y => key x ≤ key y)).image key =
          (s.image key).filter (fun k => key x ≤ k) := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨y, hy, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩,
            (Finset.mem_filter.mp hy).2⟩
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkimg, hkge⟩
        rcases Finset.mem_image.mp hkimg with ⟨y, hy, rfl⟩
        exact Finset.mem_image.mpr
          ⟨y, Finset.mem_filter.mpr ⟨hy, hkge⟩, rfl⟩
    rw [← himage]
    exact (Finset.card_image_of_injective _ hinj).symm
  calc
    s.prod (fun x => (s.filter (fun y => key x ≤ key y)).card)
        = s.prod (fun x => ((s.image key).filter (fun k => key x ≤ k)).card) := by
            exact Finset.prod_congr rfl (fun x _ => htail x)
    _ = (s.image key).prod
          (fun k => ((s.image key).filter (fun l => k ≤ l)).card) := by
            exact (Finset.prod_image
              (s := s)
              (g := key)
              (f := fun k => ((s.image key).filter (fun l => k ≤ l)).card)
              (fun a _ b _ h => hinj h)).symm
    _ = Nat.factorial (s.image key).card := by
          exact finset_prod_tail_card_eq_factorial (s.image key)
    _ = Nat.factorial s.card := by
          rw [Finset.card_image_of_injective _ hinj]

/-- The row part of a hook has cardinality `rowLength - column`. -/
theorem youngRightArmColumnCard {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    (Finset.univ.filter
      (fun j : Fin n => cell.2 ≤ j ∧ (j : ℕ) < youngRow lam cell.1)).card =
        youngRow lam cell.1 - (cell.2 : ℕ) := by
  let cols : Finset (Fin n) :=
    Finset.univ.filter
      (fun j : Fin n => cell.2 ≤ j ∧ (j : ℕ) < youngRow lam cell.1)
  have hrow_le : youngRow lam cell.1 ≤ n := by
    unfold youngRow
    split
    · exact Nat.le_of_lt_succ (lam.row _).isLt
    · exact Nat.zero_le _
  have hmap :
      cols.map Fin.valEmbedding =
        Finset.Ico (cell.2 : ℕ) (youngRow lam cell.1) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨j, hj, hval⟩
      have hj' := (Finset.mem_filter.mp hj).2
      have hvalNat : (j : ℕ) = x := hval
      rw [Finset.mem_Ico]
      constructor
      · have hle : cell.2 ≤ j := hj'.1
        have hleNat : (cell.2 : ℕ) ≤ (j : ℕ) :=
          Fin.le_iff_val_le_val.mp hle
        omega
      · omega
    · intro hx
      have hxI := Finset.mem_Ico.mp hx
      have hxn : x < n := lt_of_lt_of_le hxI.2 hrow_le
      let j : Fin n := Fin.mk x hxn
      apply Finset.mem_map.mpr
      exact ⟨j, by
        simp [cols]
        constructor
        · exact Fin.le_iff_val_le_val.mpr hxI.1
        · exact hxI.2, rfl⟩
  have hcard :
      cols.card = (Finset.Ico (cell.2 : ℕ) (youngRow lam cell.1)).card := by
    rw [hmap.symm]
    exact (Finset.card_map _).symm
  change cols.card = youngRow lam cell.1 - (cell.2 : ℕ)
  rw [hcard]
  simp

/-- The cells in the hook of `cell`, represented as the row arm union the
strictly lower column arm. -/
def youngHookCells {n : ℕ} (lam : YoungDiagram n) (cell : Fin n × Fin n) :
    Finset (Fin n × Fin n) :=
  ((Finset.univ.filter
      (fun j : Fin n => cell.2 ≤ j ∧ (j : ℕ) < youngRow lam cell.1)).image
        (fun j => (cell.1, j))) ∪
    ((Finset.univ.filter
      (fun r : Fin n => (cell.1 : ℕ) < (r : ℕ) ∧
        (cell.2 : ℕ) < youngRow lam r)).image
        (fun r => (r, cell.2)))

/-- The explicit hook-cell finset has cardinality equal to the hook length. -/
theorem youngHookCells_card {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    (youngHookCells lam cell).card = youngHookLength lam cell := by
  let rowCols : Finset (Fin n) :=
    Finset.univ.filter
      (fun j : Fin n => cell.2 ≤ j ∧ (j : ℕ) < youngRow lam cell.1)
  let lowerRows : Finset (Fin n) :=
    Finset.univ.filter
      (fun r : Fin n => (cell.1 : ℕ) < (r : ℕ) ∧
        (cell.2 : ℕ) < youngRow lam r)
  let rowCells : Finset (Fin n × Fin n) := rowCols.image (fun j => (cell.1, j))
  let lowerCells : Finset (Fin n × Fin n) := lowerRows.image (fun r => (r, cell.2))
  have hdisj : Disjoint rowCells lowerCells := by
    rw [Finset.disjoint_left]
    intro x hxrow hxlow
    rcases Finset.mem_image.mp hxrow with ⟨j, hj, hxj⟩
    rcases Finset.mem_image.mp hxlow with ⟨r, hr, hxr⟩
    have hrlt : (cell.1 : ℕ) < (r : ℕ) := (Finset.mem_filter.mp hr).2.1
    have hfirst : cell.1 = r := by
      have h := congrArg Prod.fst (hxj.trans hxr.symm)
      simpa using h
    have hval : (cell.1 : ℕ) = (r : ℕ) := congrArg Fin.val hfirst
    omega
  have hrowCols :
      rowCols.card = youngRow lam cell.1 - (cell.2 : ℕ) := by
    dsimp [rowCols]
    exact youngRightArmColumnCard lam cell
  unfold youngHookCells youngHookLength
  change (rowCells ∪ lowerCells).card =
    (youngRow lam cell.1 - (cell.2 : ℕ)) + lowerRows.card
  rw [← hrowCols]
  rw [← Finset.disjUnion_eq_union rowCells lowerCells hdisj]
  rw [Finset.card_disjUnion]
  have hrowcard : rowCells.card = rowCols.card := by
    dsimp [rowCells]
    exact Finset.card_image_of_injective _ (fun _ _ h => by
      have h2 := congrArg Prod.snd h
      simpa using h2)
  have hlowcard : lowerCells.card = lowerRows.card := by
    dsimp [lowerCells]
    exact Finset.card_image_of_injective _ (fun _ _ h => by
      have h1 := congrArg Prod.fst h
      simpa using h1)
  rw [hrowcard, hlowcard]

/-- The hook of a cell is contained in the upper tail of the cell under the
product order on row-column pairs. -/
theorem youngHookCells_subset_tail {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    youngHookCells lam cell ⊆
      (youngCells lam).filter (fun d => cell ≤ d) := by
  intro d hd
  unfold youngHookCells at hd
  rw [Finset.mem_filter]
  rw [Finset.mem_union] at hd
  rcases hd with hrow | hcol
  · rcases Finset.mem_image.mp hrow with ⟨j, hj, rfl⟩
    have hj' := (Finset.mem_filter.mp hj).2
    constructor
    · simp [youngCells, hj'.2]
    · have hle : cell ≤ (cell.1, j) := by
        exact ⟨le_rfl, hj'.1⟩
      exact hle
  · rcases Finset.mem_image.mp hcol with ⟨r, hr, rfl⟩
    have hr' := (Finset.mem_filter.mp hr).2
    constructor
    · simp [youngCells, hr'.2]
    · have hle1 : cell.1 ≤ r :=
        Fin.le_iff_val_le_val.mpr (le_of_lt hr'.1)
      have hle : cell ≤ (r, cell.2) := by
        exact ⟨hle1, le_rfl⟩
      exact hle

/-- A hook is no larger than the upper tail of its cell in the row-column
product order. -/
theorem youngHookLength_le_tail_card {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    youngHookLength lam cell ≤
      ((youngCells lam).filter (fun d => cell ≤ d)).card := by
  rw [← youngHookCells_card lam cell]
  exact Finset.card_le_card (youngHookCells_subset_tail lam cell)

/-- The hook of a cell is contained in the row-major upper tail of the cell. -/
theorem youngHookCells_subset_key_tail {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    youngHookCells lam cell ⊆
      (youngCells lam).filter
        (fun d => youngCellKey (n := n) cell ≤ youngCellKey (n := n) d) := by
  intro d hd
  unfold youngHookCells at hd
  rw [Finset.mem_filter]
  rw [Finset.mem_union] at hd
  rcases hd with hrow | hcol
  · rcases Finset.mem_image.mp hrow with ⟨j, hj, rfl⟩
    have hj' := (Finset.mem_filter.mp hj).2
    constructor
    · simp [youngCells, hj'.2]
    · have hleNat : (cell.2 : ℕ) ≤ (j : ℕ) :=
        Fin.le_iff_val_le_val.mp hj'.1
      dsimp [youngCellKey]
      exact Nat.add_le_add_left hleNat ((cell.1 : ℕ) * n)
  · rcases Finset.mem_image.mp hcol with ⟨r, hr, rfl⟩
    have hr' := (Finset.mem_filter.mp hr).2
    constructor
    · simp [youngCells, hr'.2]
    · have hleRow : (cell.1 : ℕ) ≤ (r : ℕ) := le_of_lt hr'.1
      have hmul : (cell.1 : ℕ) * n ≤ (r : ℕ) * n :=
        Nat.mul_le_mul_right n hleRow
      dsimp [youngCellKey]
      exact Nat.add_le_add_right hmul (cell.2 : ℕ)

/-- A hook is no larger than the row-major upper tail of its cell. -/
theorem youngHookLength_le_key_tail_card {n : ℕ} (lam : YoungDiagram n)
    (cell : Fin n × Fin n) :
    youngHookLength lam cell ≤
      ((youngCells lam).filter
        (fun d => youngCellKey (n := n) cell ≤ youngCellKey (n := n) d)).card := by
  rw [← youngHookCells_card lam cell]
  exact Finset.card_le_card (youngHookCells_subset_key_tail lam cell)

/-- Hook-product bound needed to show that the hook-length quotient is nonzero.

The proof injects every hook into the row-major upper tail of its base cell.
The product of those tail sizes is `n!`.
-/
theorem youngHookProduct_le_factorial_input
    (n : ℕ) (lam : YoungDiagram n) :
    (youngCells lam).prod (youngHookLength lam) ≤ Nat.factorial n := by
  calc
    (youngCells lam).prod (youngHookLength lam)
        ≤ (youngCells lam).prod
            (fun cell => ((youngCells lam).filter
              (fun d => youngCellKey (n := n) cell ≤ youngCellKey (n := n) d)).card) := by
          exact Finset.prod_le_prod
            (fun cell _ => Nat.zero_le (youngHookLength lam cell))
            (fun cell _ => youngHookLength_le_key_tail_card lam cell)
    _ = Nat.factorial (youngCells lam).card := by
          exact finset_prod_key_tail_card_eq_factorial
            (youngCells lam) (youngCellKey (n := n)) youngCellKey_injective
    _ = Nat.factorial n := by
          rw [youngCells_card lam]

/-- Positivity of the natural-number hook-length dimension proxy. -/
theorem youngDimNat_positive_hookLength_input
    (n : ℕ) (lam : YoungDiagram n) :
    0 < youngDimNat lam := by
  unfold youngDimNat
  exact Nat.div_pos
    (youngHookProduct_le_factorial_input n lam)
    (youngHookProduct_pos lam)

/-- Positivity of the real-valued Young-dimension proxy. -/
theorem youngDim_positive_from_hookLength_input (n : ℕ) :
    YoungDimensionPositiveInput n := by
  intro lam
  unfold youngDim
  exact_mod_cast youngDimNat_positive_hookLength_input n lam

/-- Once the scalar is `height / d_lambda`, the block-trace identity is just
trace divided by the positive block dimension. -/
theorem blockTraceIdentity_of_height_div_youngDim {n : ℕ}
    (height : YoungDiagram n → ℝ) :
    BlockTraceIdentityInput height (fun lam => height lam / youngDim lam) := by
  intro lam
  have hpos : 0 < youngDim lam := youngDim_positive_from_hookLength_input n lam
  have hne : youngDim lam ≠ 0 := ne_of_gt hpos
  field_simp [hne]

/-- A trace/scalar value formula implies the corresponding block-trace identity. -/
theorem blockTraceIdentity_of_traceScalarValue {n : ℕ}
    {height theta : YoungDiagram n → ℝ}
    (htrace : TraceScalarValueInput height theta) :
    BlockTraceIdentityInput height theta := by
  intro lam
  rcases htrace lam with ⟨hpos, htheta⟩
  rw [htheta]
  have hne : youngDim lam ≠ 0 := ne_of_gt hpos
  field_simp [hne]

end DictatorshipTesting
