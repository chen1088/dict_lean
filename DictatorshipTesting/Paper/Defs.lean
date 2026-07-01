import DictatorshipTesting.Basic

/-!
# Paper-level definitions

This file contains shared definitions used by the paper-numbered theorem files.
Individual numbered results live in files named after their paper number.

The definitions are intentionally concrete where possible.  For example,
matching-cube averages are finite sums over explicit near-perfect matchings, and
the Section 5 Young diagrams are finite row vectors.  This keeps elementary
proofs computational and makes every remaining external input visible as a
separate theorem rather than as an opaque definition.
-/

noncomputable section

open scoped BigOperators

namespace DictatorshipTesting

/-- Boolean functions on a symmetric group. -/
abbrev BoolFn (α : Type*) := Perm α → Bool

/-- Coerce a Boolean bit to the paper's `{0,1}` real-valued convention. -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- View a Boolean function as a real-valued `{0,1}` function. -/
def boolFnToReal {α : Type*} (f : BoolFn α) : Perm α → ℝ :=
  fun π => boolToReal (f π)

/-- Image dictators: `f π = h (π i)`. -/
def IsImageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ i : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π i)

/-- Preimage dictators: `f π = h (π⁻¹ j)`. -/
def IsPreimageDictator {α : Type*} (f : BoolFn α) : Prop :=
  ∃ j : α, ∃ h : α → Bool, ∀ π : Perm α, f π = h (π.symm j)

/-- The paper's dictator class `𝓓`. -/
def IsDictator {α : Type*} (f : BoolFn α) : Prop :=
  IsImageDictator f ∨ IsPreimageDictator f

/-- Normalized Hamming distance on Boolean functions over a finite symmetric group. -/
def hammingDist {α : Type*} [Fintype α] [DecidableEq α]
    (f g : BoolFn α) : ℝ := by
  classical
  exact
    ((Finset.univ.filter fun π : Perm α => f π ≠ g π).card : ℝ) /
      (Fintype.card (Perm α) : ℝ)

/-- Distance to the dictator class. -/
def distToDictators {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFn α) : ℝ :=
  sInf {d : ℝ | ∃ g : BoolFn α, IsDictator g ∧ d = hammingDist f g}

/-- A minimal interface for the tester promised by Theorem 1.1. -/
structure OracleTester (α : Type*) [Fintype α] [DecidableEq α] where
  queryCount : ℕ
  nonadaptive : Prop
  oneSided : Prop
  accepts : BoolFn α → Prop
  rejectsWithProbabilityAtLeast : BoolFn α → ℝ → Prop

/-- Real indicator of the one-coset `T_{ij}`. -/
def oneCosetReal {α : Type*} [DecidableEq α] (i j : α) : Perm α → ℝ :=
  fun π => if π i = j then 1 else 0

/-- The global degree-one space `U₁ = span {tᵢⱼ}`. -/
def U1 (α : Type*) [Fintype α] [DecidableEq α] : Submodule ℝ (Perm α → ℝ) :=
  Submodule.span ℝ
    (Set.range fun ij : α × α => oneCosetReal ij.1 ij.2)

/-- Squared `L²(Sₙ)` distance between real-valued functions. -/
def l2DistSq {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, (F π - G π) ^ 2) / (Fintype.card (Perm α) : ℝ)

/-- Squared distance from a function to `U₁`, equivalent to `‖f - P_{U₁} f‖²`. -/
def l2DistSqToU1 {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ G : Perm α → ℝ, G ∈ U1 α ∧ d = l2DistSq F G}

/-- Boolean cube `{0,1}ᵐ`. -/
abbrev Cube (m : ℕ) := Fin m → Bool

/-- Boolean-cube character indexed by a finite set of coordinates. -/
def cubeChar {m : ℕ} (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  ∏ r ∈ S, if x r then (-1 : ℝ) else 1

/-- Flip one coordinate of a Boolean-cube point. -/
def cubeFlip {m : ℕ} (r : Fin m) (x : Cube m) : Cube m :=
  Function.update x r (!(x r))

/-- Uniform expectation on the Boolean cube. -/
def cubeExpectation {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  (∑ x : Cube m, g x) / (Fintype.card (Cube m) : ℝ)

/-- Fourier coefficient of a real-valued function on the Boolean cube. -/
def cubeFourierCoeff {m : ℕ} (g : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  cubeExpectation fun x => g x * cubeChar S x

/-- Coordinatewise addition on the Boolean cube, written as xor. -/
def cubeXor {m : ℕ} (x y : Cube m) : Cube m :=
  fun r => x r ^^ y r

/-- The zero point of the Boolean cube. -/
def cubeZero (m : ℕ) : Cube m :=
  fun _ => false

/-- The mixed second difference on a Boolean-cube square. -/
def cubeDelta {m : ℕ} (g : Cube m → ℝ) (x u v : Cube m) : ℝ :=
  g x - g (cubeXor x u) - g (cubeXor x v) + g (cubeXor (cubeXor x u) v)

/-- Two cube directions are disjoint when no coordinate is used in both. -/
def CubeDirectionsDisjoint {m : ℕ} (u v : Cube m) : Prop :=
  ∀ r, u r = true → v r = false

/-- A Boolean cube function is constant. -/
def IsCubeConstant {m : ℕ} (g : Cube m → Bool) : Prop :=
  ∀ x y, g x = g y

/-- A Boolean cube function depends only on coordinate `r`. -/
def IsCubeJuntaAt {m : ℕ} (g : Cube m → Bool) (r : Fin m) : Prop :=
  ∀ x y, x r = y r → g x = g y

/-- A Boolean cube function depends on at most one coordinate. -/
def IsCubeOneJunta {m : ℕ} (g : Cube m → Bool) : Prop :=
  IsCubeConstant g ∨ ∃ r, IsCubeJuntaAt g r

/-- An ordered matching, with edges recorded as ordered pairs for computation. -/
structure OrderedMatching (α : Type*) [DecidableEq α] where
  edgeCount : ℕ
  left : Fin edgeCount → α
  right : Fin edgeCount → α
  left_ne_right : ∀ r, left r ≠ right r
  edges_disjoint :
    ∀ {r s : Fin edgeCount}, r ≠ s →
      left r ≠ left s ∧ left r ≠ right s ∧
        right r ≠ left s ∧ right r ≠ right s

/-- The transposition associated to one edge of an ordered matching. -/
def OrderedMatching.edgeSwap {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (r : Fin M.edgeCount) : Perm α :=
  pswap (M.left r) (M.right r)

/-- The `r`th matching transposition if the cube bit is on, otherwise identity. -/
def OrderedMatching.edgePerm {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) (r : Fin M.edgeCount) :
    Perm α :=
  if x r then M.edgeSwap r else 1

/-- The cube element `tau_x` generated by the matching transpositions. -/
def OrderedMatching.tau {α : Type*} [DecidableEq α]
    (M : OrderedMatching α) (x : Cube M.edgeCount) : Perm α :=
  (List.ofFn fun r : Fin M.edgeCount => M.edgePerm x r).prod

/-- Restrict a Boolean function on permutations to a matching cube based at `pi`. -/
def matchingCubeRestriction {α : Type*} [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α) :
    Cube M.edgeCount → Bool :=
  fun x => f (π * M.tau x)

/-- The three edge colors used by the square test, encoded as `0`, `1`, `2`. -/
abbrev CubeDirectionColor (m : ℕ) :=
  Fin m → Fin 3

/-- The `A` direction encoded by a square-test coloring. -/
def cubeColorU {m : ℕ} (c : CubeDirectionColor m) : Cube m :=
  fun r => decide (c r = (1 : Fin 3))

/-- The `B` direction encoded by a square-test coloring. -/
def cubeColorV {m : ℕ} (c : CubeDirectionColor m) : Cube m :=
  fun r => decide (c r = (2 : Fin 3))

/-- The real mixed second difference queried by one matching-cube trial. -/
def matchingTrialDelta {α : Type*} [DecidableEq α]
    (f : BoolFn α) (M : OrderedMatching α) (π : Perm α)
    (c : CubeDirectionColor M.edgeCount) : ℝ :=
  cubeDelta (fun x => boolToReal (matchingCubeRestriction f M π x))
    (cubeZero M.edgeCount) (cubeColorU c) (cubeColorV c)

/-- The real-valued mixed second difference queried by one matching-cube trial. -/
def matchingTrialDeltaReal {α : Type*} [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) (π : Perm α)
    (c : CubeDirectionColor M.edgeCount) : ℝ :=
  cubeDelta (fun x : Cube M.edgeCount => F (π * M.tau x))
    (cubeZero M.edgeCount) (cubeColorU c) (cubeColorV c)

/-- The degree-at-most-one Fourier truncation on the Boolean cube. -/
def cubeLowDegreeOnePart {m : ℕ} (g : Cube m → ℝ) : Cube m → ℝ :=
  fun x =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ 1)),
      cubeFourierCoeff g S * cubeChar S x

/-- Fourier energy on coefficients of degree at least two. -/
def cubeHighDegreeEnergy {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => 2 ≤ S.card)),
    (cubeFourierCoeff g S) ^ (2 : ℕ)

/-- Mean square of the mixed second difference under the square-test directions. -/
def cubeSquareEnergy {m : ℕ} (g : Cube m → ℝ) : ℝ :=
  (∑ x : Cube m,
      (∑ c : CubeDirectionColor m,
        (cubeDelta g x (cubeColorU c) (cubeColorV c)) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor m) : ℝ)) /
    (Fintype.card (Cube m) : ℝ)

/-- Normalized inner product on real-valued functions on a finite symmetric group. -/
def permInner {α : Type*} [Fintype α] [DecidableEq α]
    (F G : Perm α → ℝ) : ℝ :=
  (∑ π : Perm α, F π * G π) / (Fintype.card (Perm α) : ℝ)

/-- A function is locally degree one on every matching cube for `M`. -/
def IsMatchingLocalDegreeOne {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : Prop :=
  ∀ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x)) = 0

/-- Average local high-degree Fourier energy over all base permutations. -/
def matchingLocalHighDegreeEnergy {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  (∑ π : Perm α, cubeHighDegreeEnergy (fun x => F (π * M.tau x))) /
    (Fintype.card (Perm α) : ℝ)

/-- The matching-local projection `P_M`, implemented by taking the degree-at-most-one
Fourier truncation on the matching cube based at the queried permutation and
evaluating it at the cube origin.  Lemma 4.4 proves this agrees with the
representative-independent coset formula. -/
def matchingLocalProjection {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    cubeLowDegreeOnePart (fun x : Cube M.edgeCount => F (π * M.tau x))
      (cubeZero M.edgeCount)

/-- Squared error after removing the matching-local degree-one part. -/
def matchingLocalProjectionError {α : Type*} [Fintype α] [DecidableEq α]
    (F : Perm α → ℝ) (M : OrderedMatching α) : ℝ :=
  l2DistSq F (matchingLocalProjection M F)

/-- An ordered near-perfect matching on `Fin n`, with `n / 2` ordered edges.
For odd `n` this leaves one point unmatched; for even `n` it is perfect. -/
structure NearPerfectMatching (n : ℕ) where
  left : Fin (n / 2) → Fin n
  right : Fin (n / 2) → Fin n
  left_ne_right : ∀ r, left r ≠ right r
  edges_disjoint :
    ∀ {r s : Fin (n / 2)}, r ≠ s →
      left r ≠ left s ∧ left r ≠ right s ∧
        right r ≠ left s ∧ right r ≠ right s
deriving DecidableEq

noncomputable instance nearPerfectMatchingFintype (n : ℕ) :
    Fintype (NearPerfectMatching n) := by
  classical
  exact Fintype.ofInjective
    (fun M : NearPerfectMatching n => (M.left, M.right))
    (by
      intro M N h
      cases M
      cases N
      simp at h
      simp [h])

instance nearPerfectMatchingNonempty (n : ℕ) : Nonempty (NearPerfectMatching n) := by
  let left : Fin (n / 2) → Fin n :=
    fun r => ⟨2 * (r : ℕ), by
      have hr : (r : ℕ) < n / 2 := r.isLt
      omega⟩
  let right : Fin (n / 2) → Fin n :=
    fun r => ⟨2 * (r : ℕ) + 1, by
      have hr : (r : ℕ) < n / 2 := r.isLt
      omega⟩
  refine ⟨{ left := left, right := right, left_ne_right := ?_, edges_disjoint := ?_ }⟩
  · intro r h
    have hnat := congrArg Fin.val h
    dsimp [left, right] at hnat
    omega
  · intro r s hrs
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left] at hnat
      exact hrs (Fin.ext (by omega))
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left, right] at hnat
      omega
    constructor
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [left, right] at hnat
      omega
    · intro h
      have hnat := congrArg Fin.val h
      dsimp [right] at hnat
      exact hrs (Fin.ext (by omega))

/-- View a near-perfect matching as the generic ordered matching structure. -/
def NearPerfectMatching.toOrdered {n : ℕ}
    (M : NearPerfectMatching n) : OrderedMatching (Fin n) where
  edgeCount := n / 2
  left := M.left
  right := M.right
  left_ne_right := M.left_ne_right
  edges_disjoint := by
    intro r s hrs
    exact M.edges_disjoint hrs

/-- Mean, over a uniformly random near-perfect matching, of `||(I-P_M)F||_2^2`. -/
def matchingMeanProjectionError {n : ℕ}
    (F : Perm (Fin n) → ℝ) : ℝ :=
  (∑ M : NearPerfectMatching n,
    matchingLocalProjectionError F M.toOrdered) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

/-- Mean square of the alternating sum queried by one matching-cube trial. -/
def oneTrialDeltaSqExpectation {n : ℕ}
    (F : Perm (Fin n) → ℝ) : ℝ :=
  (∑ M : NearPerfectMatching n,
    (∑ π : Perm (Fin n),
      (∑ c : CubeDirectionColor (n / 2),
        (matchingTrialDeltaReal F M.toOrdered π c) ^ (2 : ℕ)) /
          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ)) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

/-- Rejection probability of one matching-cube trial on a Boolean oracle. -/
def oneTrialRejectProbability {n : ℕ}
    (f : BoolFn (Fin n)) : ℝ :=
  (∑ M : NearPerfectMatching n,
    (∑ π : Perm (Fin n),
      (∑ c : CubeDirectionColor (n / 2),
        if matchingTrialDelta f M.toOrdered π c = 0 then (0 : ℝ) else 1) /
          (Fintype.card (CubeDirectionColor (n / 2)) : ℝ)) /
        (Fintype.card (Perm (Fin n)) : ℝ)) /
      (Fintype.card (NearPerfectMatching n) : ℝ)

/-- Low-character convolution side of the local projection formula.

This is the sum of the matching-cube Fourier idempotents indexed by characters
of support size at most one, evaluated on the matching cube based at `π`. -/
def matchingLowConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin M.edgeCount) => S.card ≤ 1)),
      cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
        cubeChar S (cubeZero M.edgeCount)

/-- High-character convolution side of `I - P_M`.

This is the complementary sum of the matching-cube Fourier idempotents indexed
by characters of support size at least two. -/
def matchingHighConvolution {α : Type*} [Fintype α] [DecidableEq α]
    (M : OrderedMatching α) (F : Perm α → ℝ) : Perm α → ℝ :=
  fun π =>
    ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin M.edgeCount) => 2 ≤ S.card)),
      cubeFourierCoeff (fun x : Cube M.edgeCount => F (π * M.tau x)) S *
        cubeChar S (cubeZero M.edgeCount)

/-- A Young diagram with `n` boxes, represented by its row lengths.  The row
vector has length `n`, which is enough because a partition of `n` has at most
`n` nonzero rows; each row length is bounded by `n`. -/
structure YoungDiagram (n : ℕ) where
  row : Fin n → Fin (n + 1)
  nonincreasing :
    ∀ {i j : Fin n}, (i : ℕ) ≤ (j : ℕ) → (row j : ℕ) ≤ (row i : ℕ)
  sum_rows : (∑ i : Fin n, (row i : ℕ)) = n
deriving DecidableEq

noncomputable instance youngDiagramFintype (n : ℕ) : Fintype (YoungDiagram n) := by
  classical
  exact Fintype.ofInjective YoungDiagram.row (by
    intro lam mu h
    cases lam
    cases mu
    simp at h
    simp [h])

/-- Row length of a Young diagram, extended by zero past the last represented
row.  Row and column indices are zero-based. -/
def youngRow {n : ℕ} (lam : YoungDiagram n) (i : ℕ) : ℕ :=
  if h : i < n then (lam.row ⟨i, h⟩ : ℕ) else 0

/-- The cells of a Young diagram, represented as zero-based row-column pairs. -/
def youngCells {n : ℕ} (lam : YoungDiagram n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun cell : Fin n × Fin n =>
    (cell.2 : ℕ) < youngRow lam cell.1)

/-- Hook length of a cell in a Young diagram. -/
def youngHookLength {n : ℕ} (lam : YoungDiagram n) (cell : Fin n × Fin n) : ℕ :=
  (youngRow lam cell.1 - (cell.2 : ℕ)) +
    (Finset.univ.filter (fun r : Fin n =>
      (cell.1 : ℕ) < (r : ℕ) ∧ (cell.2 : ℕ) < youngRow lam r)).card

/-- Natural-number hook-length dimension formula. -/
def youngDimNat {n : ℕ} (lam : YoungDiagram n) : ℕ :=
  Nat.factorial n / (youngCells lam).prod (youngHookLength lam)

/-- Dimension of the Specht module indexed by a Young diagram, via the hook
length formula. -/
def youngDim {n : ℕ} (lam : YoungDiagram n) : ℝ :=
  youngDimNat lam

/-- The one-row Young diagram. -/
def IsOneRow {n : ℕ} (lam : YoungDiagram n) : Prop :=
  youngRow lam 0 = n

/-- The standard Young diagram `(n-1,1)`. -/
def IsStandard {n : ℕ} (lam : YoungDiagram n) : Prop :=
  2 ≤ n ∧ youngRow lam 0 = n - 1 ∧ youngRow lam 1 = 1

/-- `mu` is contained in `lam` as a Young diagram. -/
def IsYoungSubdiagram {n k : ℕ} (mu : YoungDiagram k) (lam : YoungDiagram n) : Prop :=
  ∀ i : Fin n, youngRow mu i ≤ youngRow lam i

/-- `lam / mu` is a horizontal two-strip. -/
def IsHorizontalTwoStripChild {n k : ℕ} (lam : YoungDiagram n)
    (mu : YoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam ((i : ℕ) + 1) ≤ youngRow mu i

/-- `lam / mu` is a vertical two-strip. -/
def IsVerticalTwoStripChild {n k : ℕ} (lam : YoungDiagram n)
    (mu : YoungDiagram k) : Prop :=
  k + 2 = n ∧
    IsYoungSubdiagram mu lam ∧
      ∀ i : Fin n, youngRow lam i ≤ youngRow mu i + 1

/-- `lam / mu` consists of one removable box. -/
def IsOneBoxChild {n k : ℕ} (lam : YoungDiagram n) (mu : YoungDiagram k) : Prop :=
  k + 1 = n ∧ IsYoungSubdiagram mu lam

/-- Horizontal two-strip children in the domino branching rule. -/
def horizontalTwoStripChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 2) =>
    IsHorizontalTwoStripChild lam mu)

/-- Vertical two-strip children in the domino branching rule. -/
def verticalTwoStripChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 2)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 2) =>
    IsVerticalTwoStripChild lam mu)

/-- One-box children in the ordinary branching rule. -/
def oneBoxChildren {n : ℕ}
    (lam : YoungDiagram n) : Finset (YoungDiagram (n - 1)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (n - 1) =>
    IsOneBoxChild lam mu)

/-- Horizontal two-strip children specialized to diagrams with `2*m` boxes. -/
def horizontalTwoStripChildrenEven (m : ℕ)
    (lam : YoungDiagram (2 * m)) : Finset (YoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * (m - 1)) =>
    IsHorizontalTwoStripChild lam mu)

/-- Vertical two-strip children specialized to diagrams with `2*m` boxes. -/
def verticalTwoStripChildrenEven (m : ℕ)
    (lam : YoungDiagram (2 * m)) : Finset (YoungDiagram (2 * (m - 1))) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * (m - 1)) =>
    IsVerticalTwoStripChild lam mu)

/-- One-box children specialized to diagrams with `2*m+1` boxes. -/
def oneBoxChildrenOdd (m : ℕ)
    (lam : YoungDiagram (2 * m + 1)) : Finset (YoungDiagram (2 * m)) := by
  classical
  exact Finset.univ.filter (fun mu : YoungDiagram (2 * m) =>
    IsOneBoxChild lam mu)

/-- Number of weight-zero entries in the even matching-branching multiset. -/
def zEven : (m : ℕ) → YoungDiagram (2 * m) → ℝ
  | 0, _ => 1
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
        (fun mu => zEven m mu)

/-- Number of weight-at-least-two entries in the even matching-branching multiset. -/
def hEven : (m : ℕ) → YoungDiagram (2 * m) → ℝ
  | 0, _ => 0
  | m + 1, lam =>
      (horizontalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => hEven m mu) +
        (verticalTwoStripChildrenEven (m + 1) lam).sum
          (fun mu => youngDim mu - zEven m mu)

/-- Number of weight-at-least-two entries in the odd matching-branching multiset. -/
def hOdd (m : ℕ) (lam : YoungDiagram (2 * m + 1)) : ℝ :=
  (oneBoxChildrenOdd m lam).sum (fun mu => hEven m mu)

/-- The spectral gap assertion with constant `c`. -/
def MatchingSpectralGapConstant (n : ℕ) (c : ℝ) : Prop :=
  ∀ F : Perm (Fin n) → ℝ,
    c * l2DistSqToU1 F ≤ matchingMeanProjectionError F

end DictatorshipTesting
