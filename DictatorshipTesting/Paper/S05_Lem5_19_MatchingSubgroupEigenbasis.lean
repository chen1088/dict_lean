import DictatorshipTesting.Paper.Aux_YoungMatchingOperators
import DictatorshipTesting.Paper.S05_Def5_18_MatchingCharacters
import DictatorshipTesting.Paper.S05_Lem5_36_OddCertificate

/-!
Paper statement: Lemma 5.19 (`lem:matching-restriction-X`)
Title in paper: Matching subgroup eigenbasis.

Legacy scalar-shadow file for the rewritten Section 5 statement.

Status: the paper's Lemma 5.19 is the full Specht-module restriction statement
obtained from repeated Pieri/Littlewood--Richardson branching.  The current
Lean file does not formalize Specht modules or restriction functors; it proves
only the scalar/multiplicity shadow used downstream by the scaffold.
-/

/-!
# Matching-restriction scalar shadow

The paper's full statement says that, after restricting the Specht module
indexed by `lambda` to the matching subgroup `A_M ≃ (Z / 2Z)^m`, the local
character-weight multiset is the recursively defined multiset counted by
`zEven`, `hEven`, and `hOdd`.

The current Lean vocabulary does not yet contain Specht modules or restriction
functors.  The statements below therefore do not claim to be the full
restriction theorem.  They record the scalar bounds needed by the rest of the
scaffold, and those scalar consequences are proved from the finite certificate
bounds already formalized.
-/

noncomputable section

namespace DictatorshipTesting

/-- Lemma 5.19 matching-operator component: a canonical even matching edge
operator is an involution. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorEven_involutive
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven r f) = f := by
  exact canonicalMatchingYoungOperatorEven_involutive r f

/-- Lemma 5.19 matching-operator component: distinct canonical even matching
edge operators commute. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorEven_comm
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (canonicalMatchingYoungOperatorEven s f) =
      canonicalMatchingYoungOperatorEven s
        (canonicalMatchingYoungOperatorEven r f) := by
  exact canonicalMatchingYoungOperatorEven_comm hrs f

/-- Lemma 5.19 matching-operator component: a canonical odd matching edge
operator is an involution. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorOdd_involutive
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd r f) = f := by
  exact canonicalMatchingYoungOperatorOdd_involutive r f

/-- Lemma 5.19 matching-operator component: distinct canonical odd matching
edge operators commute. -/
theorem S05_Lem5_19_canonicalMatchingYoungOperatorOdd_comm
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {r s : Fin m} (hrs : r ≠ s) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (canonicalMatchingYoungOperatorOdd s f) =
      canonicalMatchingYoungOperatorOdd s
        (canonicalMatchingYoungOperatorOdd r f) := by
  exact canonicalMatchingYoungOperatorOdd_comm hrs f

/-- Lemma 5.19 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_19_matchingEdge_plusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T + canonicalMatchingYoungOperatorEven r f T) =
      fun T => f T + canonicalMatchingYoungOperatorEven r f T := by
  exact canonicalMatchingYoungOperatorEven_plusEigenVec r f

/-- Lemma 5.19 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an even matching edge. -/
theorem S05_Lem5_19_matchingEdge_minusEigenVec_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorEven r
        (fun T => f T - canonicalMatchingYoungOperatorEven r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorEven r f T) := by
  exact canonicalMatchingYoungOperatorEven_minusEigenVec r f

/-- Lemma 5.19 matching-edge eigenspace component: `v + A_r v` is a `+1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_19_matchingEdge_plusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T + canonicalMatchingYoungOperatorOdd r f T) =
      fun T => f T + canonicalMatchingYoungOperatorOdd r f T := by
  exact canonicalMatchingYoungOperatorOdd_plusEigenVec r f

/-- Lemma 5.19 matching-edge eigenspace component: `v - A_r v` is a `-1`
eigenvector for an odd matching edge. -/
theorem S05_Lem5_19_matchingEdge_minusEigenVec_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (r : Fin m) (f : TableauSpace lam) :
    canonicalMatchingYoungOperatorOdd r
        (fun T => f T - canonicalMatchingYoungOperatorOdd r f T) =
      fun T => - (f T - canonicalMatchingYoungOperatorOdd r f T) := by
  exact canonicalMatchingYoungOperatorOdd_minusEigenVec r f

/-- Lemma 5.19 matching-cube component: the zero cube element acts trivially in
the even canonical matching action. -/
theorem S05_Lem5_19_canonicalMatchingCubeOperatorEven_zero
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)} :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorEven_zero

/-- Lemma 5.19 matching-cube component: the zero cube element acts trivially in
the odd canonical matching action. -/
theorem S05_Lem5_19_canonicalMatchingCubeOperatorOdd_zero
    {m : Nat} {lam : YoungDiagram (2 * m + 1)} :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeZero m) = id := by
  exact canonicalMatchingCubeOperatorOdd_zero

/-- Lemma 5.19 matching-cube component: the even canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_19_canonicalMatchingCubeOperatorEven_xor
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorEven (lam := lam) x
        (canonicalMatchingCubeOperatorEven (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorEven_xor x y

/-- Lemma 5.19 matching-cube component: the odd canonical matching operators
respect the cube XOR law. -/
theorem S05_Lem5_19_canonicalMatchingCubeOperatorOdd_xor
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (x y : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) (cubeXor x y) =
      fun f => canonicalMatchingCubeOperatorOdd (lam := lam) x
        (canonicalMatchingCubeOperatorOdd (lam := lam) y f) := by
  exact canonicalMatchingCubeOperatorOdd_xor x y

/-- Lemma 5.19 matching-character component: simultaneous even matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorEven
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorEven f R

/-- Lemma 5.19 matching-character component: simultaneous odd matching-edge
eigenvectors are indexed by a character support. -/
abbrev S05_IsMatchingEigenvectorOdd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (f : TableauSpace lam) (R : Finset (Fin m)) : Prop :=
  IsMatchingEigenvectorOdd f R

/-- Lemma 5.19 matching-character component: on an even simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_19_matchingCube_character_action_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorEven f R) (x : Cube m) :
    canonicalMatchingCubeOperatorEven (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorEven_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.19 matching-character component: on an odd simultaneous
matching-edge eigenspace, the cube action is the matching character. -/
theorem S05_Lem5_19_matchingCube_character_action_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    {f : TableauSpace lam} {R : Finset (Fin m)}
    (hf : S05_IsMatchingEigenvectorOdd f R) (x : Cube m) :
    canonicalMatchingCubeOperatorOdd (lam := lam) x f =
      S05_matchingCharacter R x • f := by
  exact canonicalMatchingCubeOperatorOdd_apply_character_of_isMatchingEigenvector
    hf x

/-- Lemma 5.19 one-edge component: an even matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_19_matchingEdge_basis_sameRow_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow T r hrow

/-- Lemma 5.19 one-edge component: an even matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_19_matchingEdge_basis_sameCol_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol T r hcol

/-- Lemma 5.19 one-edge eigenspace component: in the even case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_19_matchingEdge_sameRow_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameRow_eigen T r hrow

/-- Lemma 5.19 one-edge eigenspace component: in the even case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_19_matchingEdge_sameCol_eigen_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorEven_basis_sameCol_eigen T r hcol

/-- Lemma 5.19 one-edge component: in an even swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_19_matchingEdge_basis_swappable_self_value_even
    {m : Nat} {lam : YoungDiagram ((2 * m - 1) + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorEven r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorEven_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.19 one-edge component: in an even swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_19_matchingEdge_basis_swappable_swap_value_even
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

/-- Lemma 5.19 one-edge component: an odd matching edge fixes a same-row
tableau basis vector. -/
theorem S05_Lem5_19_matchingEdge_basis_sameRow_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow T r hrow

/-- Lemma 5.19 one-edge component: an odd matching edge negates a same-column
tableau basis vector. -/
theorem S05_Lem5_19_matchingEdge_basis_sameCol_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      fun S => -tableauBasisVec T S := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol T r hcol

/-- Lemma 5.19 one-edge eigenspace component: in the odd case, a same-row
tableau basis vector has eigenvalue `1`. -/
theorem S05_Lem5_19_matchingEdge_sameRow_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow : adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameRow_eigen T r hrow

/-- Lemma 5.19 one-edge eigenspace component: in the odd case, a same-column
tableau basis vector has eigenvalue `-1`. -/
theorem S05_Lem5_19_matchingEdge_sameCol_eigen_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hcol : adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) =
      (-1 : ℝ) • tableauBasisVec T := by
  exact canonicalMatchingYoungOperatorOdd_basis_sameCol_eigen T r hcol

/-- Lemma 5.19 one-edge component: in an odd swappable edge, the diagonal
coordinate is the Young axial coefficient. -/
theorem S05_Lem5_19_matchingEdge_basis_swappable_self_value_odd
    {m : Nat} {lam : YoungDiagram (2 * m + 1)}
    (T : StandardYoungTableau lam) (r : Fin m)
    (hrow_ne : ¬ adjacentSameRow T (canonicalNearMatchingAdjacentIndex m r))
    (hcol_ne : ¬ adjacentSameCol T (canonicalNearMatchingAdjacentIndex m r)) :
    canonicalMatchingYoungOperatorOdd r (tableauBasisVec T) T =
      youngAdjacentDiagCoeff T (canonicalNearMatchingAdjacentIndex m r) := by
  exact canonicalMatchingYoungOperatorOdd_basis_swappable_self_value
    T r hrow_ne hcol_ne

/-- Lemma 5.19 one-edge component: in an odd swappable edge, the swapped
coordinate is the Young off-diagonal coefficient. -/
theorem S05_Lem5_19_matchingEdge_basis_swappable_swap_value_odd
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

/-- Even matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionEvenInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m),
    0 ≤ hEven m lam ∧ hEven m lam ≤ youngDim lam

/-- Odd matching-restriction input, in the scalar vocabulary currently
available in Lean. -/
def MatchingRestrictionOddInput (m : ℕ) : Prop :=
  ∀ lam : YoungDiagram (2 * m + 1),
    0 ≤ hOdd m lam ∧ hOdd m lam ≤ youngDim lam

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
