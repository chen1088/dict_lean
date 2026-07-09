import DictatorshipTesting.Paper.S05_Int_YoungMatchingOperators
import DictatorshipTesting.Paper.Defs.S05_Def5_15_MatchingCharacters
import DictatorshipTesting.Paper.Defs.S05_Def5_16_IsMatchingEigenvectorEven
import DictatorshipTesting.Paper.Defs.S05_Def5_17_IsMatchingEigenvectorOdd
import DictatorshipTesting.Paper.Defs.S05_Def5_18_MatchingRestrictionEvenInput
import DictatorshipTesting.Paper.Defs.S05_Def5_19_MatchingRestrictionOddInput
import DictatorshipTesting.Paper.S05_Lem5_26_OddCertificate

/-
Direct reverse imports:
- `DictatorshipTesting`
- `DictatorshipTesting.Paper.S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock`
-/


/-!
Paper statement: Lemma 5.10 (`lem:matching-restriction-X`)
Title in paper: Matching subgroup eigenbasis.

Status: proven. The concrete matching-operator and sign-projection interfaces
are proved below; the full Specht/Pieri restriction content is bundled into the
spectral-block model boundary.
-/

/-!
# Matching-restriction scalar shadow

The paper's full statement says that, after restricting the Specht module
indexed by `lambda` to the matching subgroup `A_M ≃ (Z / 2Z)^m`, the local
character-weight multiset is the recursively defined multiset counted by
`zEven`, `hEven`, and `hOdd`.

The current Lean vocabulary does not yet contain Specht modules or restriction
functors.  The statements below therefore do not claim to be the full
restriction theorem.  They record concrete matching-operator and matching-cube
character components, plus scalar-bound interfaces used by the rest of the
scaffold.  The full restriction theorem remains an external
representation-theoretic input.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.10 matching-operator component: a canonical even matching edge
operator is an involution. -/
theorem S05_Lem5_10_canonicalMatchingYoungOperatorEven_involutive
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven r f) = f := by
  exact canonicalMatchingYoungOperatorEven_involutive r f

/-- Lemma 5.10 matching-operator component: distinct canonical even matching
edge operators commute. -/
theorem S05_Lem5_10_canonicalMatchingYoungOperatorEven_comm
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven s f) =
      canonicalMatchingYoungOperatorEven s
        (canonicalMatchingYoungOperatorEven r f) := by
  exact canonicalMatchingYoungOperatorEven_comm hrs f

/-- Lemma 5.10 matching-operator component: a canonical odd matching edge
operator is an involution. -/
theorem S05_Lem5_10_canonicalMatchingYoungOperatorOdd_involutive
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd r f) = f := by
  exact canonicalMatchingYoungOperatorOdd_involutive r f

/-- Lemma 5.10 matching-operator component: distinct canonical odd matching
edge operators commute. -/
theorem S05_Lem5_10_canonicalMatchingYoungOperatorOdd_comm
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd s f) =
      canonicalMatchingYoungOperatorOdd s
        (canonicalMatchingYoungOperatorOdd r f) := by
  exact canonicalMatchingYoungOperatorOdd_comm hrs f

/-- Lemma 5.10 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_10_matchingEdge_plusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T + canonicalMatchingYoungOperatorEven r f T) =
      fun T => f T + canonicalMatchingYoungOperatorEven r f T := by
  exact canonicalMatchingYoungOperatorEven_plusEigenVec r f

/-- Lemma 5.10 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_10_matchingEdge_minusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T - canonicalMatchingYoungOperatorEven r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorEven r f T) := by
  exact canonicalMatchingYoungOperatorEven_minusEigenVec r f

/-- Lemma 5.10 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_10_matchingEdge_plusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T + canonicalMatchingYoungOperatorOdd r f T) =
      fun T => f T + canonicalMatchingYoungOperatorOdd r f T := by
  exact canonicalMatchingYoungOperatorOdd_plusEigenVec r f

/-- Lemma 5.10 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_10_matchingEdge_minusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T - canonicalMatchingYoungOperatorOdd r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorOdd r f T) := by
  exact canonicalMatchingYoungOperatorOdd_minusEigenVec r f

/-- Lemma 5.10 matching-cube component: the zero cube element acts trivially in
the even canonical matching action. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorEven_zero
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)} :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorEven_zero

/-- Lemma 5.10 matching-cube component: the zero cube element acts trivially in
the odd canonical matching action. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorOdd_zero
    {m : Nat} {lam : YoungDiagram (2 * m + 1)} :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorOdd_zero

/-- Lemma 5.10 matching-cube component: the even canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorEven_xor
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorEven_xor x y

/-- Lemma 5.10 matching-cube component: the odd canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorOdd_xor
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorOdd (lam := lam) x
        (canonicalMatchingCubeOperatorOdd (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorOdd_xor x y

/-- Lemma 5.10 matching-cube component: the even canonical matching-cube
operator is the fixed ordered product of the selected edge operators. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorEven_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorEven (lam := lam) r)
        x (List.finRange m) := by
  exact canonicalMatchingCubeOperatorEven_eq_indexedProduct x

/-- Lemma 5.10 matching-cube component: the odd canonical matching-cube
operator is the fixed ordered product of the selected edge operators. -/
theorem S05_Lem5_10_canonicalMatchingCubeOperatorOdd_eq_indexedProduct
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x =
      indexedOperatorListProduct
        (fun r : Fin m => canonicalMatchingYoungOperatorOdd (lam := lam) r)
        x (List.finRange m) := by
  exact canonicalMatchingCubeOperatorOdd_eq_indexedProduct x

/-- Lemma 5.10 matching-character component: the product of selected edge
signs is the matching character. -/
theorem S05_Lem5_10_matchingEdgeSign_finRange_product_eq_matchingCharacter
    {m : Nat} (R : Finset (Fin m)) (x : Cube m) :
    ((List.finRange m).map
      (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod =
        S05_matchingCharacter R x := by
  exact matchingEdgeSign_finRange_product_eq_cubeChar R x

/-- Lemma 5.10 matching-character component: on an even simultaneous
matching-edge eigenspace, the cube action is the product of selected edge
signs. -/
theorem S05_Lem5_10_matchingCube_product_action_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  exact canonicalMatchingCubeOperatorEven_apply_of_isMatchingEigenvector hf x

/-- Lemma 5.10 matching-character component: on an odd simultaneous
matching-edge eigenspace, the cube action is the product of selected edge
signs. -/
theorem S05_Lem5_10_matchingCube_product_action_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      ((List.finRange m).map
        (fun r : Fin m => if x r then matchingEdgeSign R r else 1)).prod • f := by
  exact canonicalMatchingCubeOperatorOdd_apply_of_isMatchingEigenvector hf x

/-- Lemma 5.10 matching-character component: on an even simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_10_matchingCube_character_action_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorEven_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.10 matching-character component: on an odd simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_10_matchingCube_character_action_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.10 projection component: the one-edge even plus projection lands in
the `+1` eigenspace of that edge. -/
theorem S05_Lem5_10_matchingEdgePlusProjectionEven_isPlusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgePlusProjectionEven r f) =
      matchingEdgePlusProjectionEven r f := by
  exact matchingEdgePlusProjectionEven_isPlusEigen r f

/-- Lemma 5.10 projection component: the one-edge even minus projection lands
in the `-1` eigenspace of that edge. -/
theorem S05_Lem5_10_matchingEdgeMinusProjectionEven_isMinusEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeMinusProjectionEven r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionEven r f := by
  exact matchingEdgeMinusProjectionEven_isMinusEigen r f

/-- Lemma 5.10 projection component: the one-edge odd plus projection lands in
the `+1` eigenspace of that edge. -/
theorem S05_Lem5_10_matchingEdgePlusProjectionOdd_isPlusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgePlusProjectionOdd r f) =
      matchingEdgePlusProjectionOdd r f := by
  exact matchingEdgePlusProjectionOdd_isPlusEigen r f

/-- Lemma 5.10 projection component: the one-edge odd minus projection lands
in the `-1` eigenspace of that edge. -/
theorem S05_Lem5_10_matchingEdgeMinusProjectionOdd_isMinusEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeMinusProjectionOdd r f) =
      (-1 : ℝ) • matchingEdgeMinusProjectionOdd r f := by
  exact matchingEdgeMinusProjectionOdd_isMinusEigen r f

/-- Lemma 5.10 projection component: projecting to the `+1` eigenspace of one
even matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgePlusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgePlusProjectionEven r f) =
      c • matchingEdgePlusProjectionEven r f := by
  exact matchingEdgePlusProjectionEven_preserves_otherEigen hrs hf

/-- Lemma 5.10 projection component: projecting to the `-1` eigenspace of one
even matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgeMinusProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s (matchingEdgeMinusProjectionEven r f) =
      c • matchingEdgeMinusProjectionEven r f := by
  exact matchingEdgeMinusProjectionEven_preserves_otherEigen hrs hf

/-- Lemma 5.10 projection component: projecting to the `+1` eigenspace of one
odd matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgePlusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgePlusProjectionOdd r f) =
      c • matchingEdgePlusProjectionOdd r f := by
  exact matchingEdgePlusProjectionOdd_preserves_otherEigen hrs hf

/-- Lemma 5.10 projection component: projecting to the `-1` eigenspace of one
odd matching edge preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgeMinusProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s (matchingEdgeMinusProjectionOdd r f) =
      c • matchingEdgeMinusProjectionOdd r f := by
  exact matchingEdgeMinusProjectionOdd_preserves_otherEigen hrs hf

/-- Lemma 5.10 projection component: the sign-selected even one-edge
projection has the edge eigenvalue prescribed by the support. -/
theorem S05_Lem5_10_matchingEdgeSignProjectionEven_isMatchingEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (matchingEdgeSignProjectionEven R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionEven R r f := by
  exact matchingEdgeSignProjectionEven_isMatchingEigen R r f

/-- Lemma 5.10 projection component: the sign-selected odd one-edge projection
has the edge eigenvalue prescribed by the support. -/
theorem S05_Lem5_10_matchingEdgeSignProjectionOdd_isMatchingEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (matchingEdgeSignProjectionOdd R r f) =
      matchingEdgeSign R r • matchingEdgeSignProjectionOdd R r f := by
  exact matchingEdgeSignProjectionOdd_isMatchingEigen R r f

/-- Lemma 5.10 projection component: the sign-selected even one-edge projection
preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgeSignProjectionEven_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorEven s f = c • f) :
    canonicalMatchingYoungOperatorEven s
        (matchingEdgeSignProjectionEven R r f) =
      c • matchingEdgeSignProjectionEven R r f := by
  exact matchingEdgeSignProjectionEven_preserves_otherEigen R hrs hf

/-- Lemma 5.10 projection component: the sign-selected odd one-edge projection
preserves every other edge eigenvalue. -/
theorem S05_Lem5_10_matchingEdgeSignProjectionOdd_preserves_otherEigen
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) {r s : Fin m} (hrs : r ≠ s)
    {c : ℝ} {f : TableauSpace lam}
    (hf : canonicalMatchingYoungOperatorOdd s f = c • f) :
    canonicalMatchingYoungOperatorOdd s
        (matchingEdgeSignProjectionOdd R r f) =
      c • matchingEdgeSignProjectionOdd R r f := by
  exact matchingEdgeSignProjectionOdd_preserves_otherEigen R hrs hf

/-- Lemma 5.10 projection component: the iterated even support-selected
projection is a simultaneous matching-edge eigenvector. -/
theorem S05_Lem5_10_matchingSignProjectionEven_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    S05_IsMatchingEigenvectorEven (matchingSignProjectionEven R f) R := by
  exact matchingSignProjectionEven_isMatchingEigenvector R f

/-- Lemma 5.10 projection component: the iterated odd support-selected
projection is a simultaneous matching-edge eigenvector. -/
theorem S05_Lem5_10_matchingSignProjectionOdd_isMatchingEigenvector
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (R : Finset (Fin m)) (f : TableauSpace lam) :
    S05_IsMatchingEigenvectorOdd (matchingSignProjectionOdd R f) R := by
  exact matchingSignProjectionOdd_isMatchingEigenvector R f

/-- Lemma 5.10 one-edge component: an even matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_10_matchingEdge_basis_sameRow_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow T r hrow

/-- Lemma 5.10 one-edge component: an even matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_10_matchingEdge_basis_sameCol_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol T r hcol

/-- Lemma 5.10 one-edge eigenspace component: in the even case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_10_matchingEdge_sameRow_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow_eigen T r hrow

/-- Lemma 5.10 one-edge eigenspace component: in the even case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_10_matchingEdge_sameCol_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol_eigen T r hcol

/-- Lemma 5.10 one-edge component: in an even swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_10_matchingEdge_basis_swappable_self_value_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorEven_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.10 one-edge component: in an even swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_10_matchingEdge_basis_swappable_swap_value_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorEven_basis_swappable_swap_value
    T r hrow_ne hcol_ne

/-- Lemma 5.10 one-edge component: an odd matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_10_matchingEdge_basis_sameRow_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow T r hrow

/-- Lemma 5.10 one-edge component: an odd matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_10_matchingEdge_basis_sameCol_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol T r hcol

/-- Lemma 5.10 one-edge eigenspace component: in the odd case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_10_matchingEdge_sameRow_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow_eigen T r hrow

/-- Lemma 5.10 one-edge eigenspace component: in the odd case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_10_matchingEdge_sameCol_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol_eigen T r hcol

/-- Lemma 5.10 one-edge component: in an odd swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_10_matchingEdge_basis_swappable_self_value_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorOdd_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.10 one-edge component: in an odd swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_10_matchingEdge_basis_swappable_swap_value_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T)
        (adjacentSwapTableau T (canonicalNearMatchingAdjacentIndex m r)
          hrow_ne hcol_ne) =
      youngAdjacentOffCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorOdd_basis_swappable_swap_value
    T r hrow_ne hcol_ne

/-- Scalar consequence for even matching subgroups. -/
theorem matchingRestriction_even_specht_pieri_input
    [TwoStripDimensionBranchingAssumption] (m : ℕ) :
    MatchingRestrictionEvenInput m := by
  intro lam
  exact ⟨hEven_nonneg m lam, hEven_le_youngDim m lam⟩

/-- Scalar consequence for odd matching subgroups. -/
theorem matchingRestriction_odd_specht_pieri_input
    [TwoStripDimensionBranchingAssumption]
    [OneBoxDimensionBranchingPositiveAssumption] (m : ℕ) :
    MatchingRestrictionOddInput m := by
  intro lam
  exact ⟨hOdd_nonneg m lam, hOdd_le_youngDim m lam⟩

end DictatorshipTesting
