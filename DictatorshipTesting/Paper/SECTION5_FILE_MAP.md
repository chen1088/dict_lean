# Section 5 File Map

The compiled paper has separate definition and theorem-like counters.

Dependency convention: every numbered predecessor shown in the dependency
viewer is imported directly by the corresponding paper-facing module. Internal
modules may retain reusable proof machinery, but they do not replace the
visible numbered dependency chain.

## Definitions

| Statement | Title | Lean file(s) |
| --- | --- | --- |
| Definition 5.1 | Young diagrams and boxes | `Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean` |
| Definition 5.2 | Removable corners and one-box removals | `Defs/S05_Def5_02_RemovableCorners.lean` |
| Definition 5.3 | Standard Young tableaux and occupation notation | `Defs/S05_Def5_03_StandardTableaux.lean` |
| Definition 5.4 | Tableau coordinate space | `Defs/S05_Def5_04_TableauCoordinateSpace.lean` |
| Definition 5.5 | Contents and adjacent operators | `Defs/S05_Def5_05_ContentAndAdjacentOperators.lean` |
| Definition 5.6 | Young matrix coefficients, blocks, and energies | `Defs/S05_Def5_06a_YoungBlock.lean`, `Defs/S05_Def5_06b_YoungMatrixCoefficients.lean`, `Defs/S05_Def5_06c_YoungBlockComponentsAndEnergies.lean` |
| Definition 5.7 | Branching data | `Defs/S05_Def5_07a_TwoBoxRemovals.lean`, `Defs/S05_Def5_07b_SignedTwoBoxRemovals.lean`, `Defs/S05_Def5_07c_OneBoxRemovals.lean` |
| Definition 5.8 | Signed two-box extension spaces | `Defs/S05_Def5_08_SignedTwoBoxExtensionSpaces.lean` |
| Definition 5.9 | One-box deletion spaces | `Defs/S05_Def5_09_OneBoxDeletionSpaces.lean` |
| Definition 5.10 | Matching sign-pattern multisets and heights | `Defs/S05_Def5_10a_EvenSignPatternMultiset.lean`, `Defs/S05_Def5_10b_OddSignPatternMultiset.lean` |
| Definition 5.11 | Matching characters and eigenvectors | `Defs/S05_Def5_11a_MatchingCharacters.lean`, `Defs/S05_Def5_11b_IsMatchingEigenvectorEven.lean`, `Defs/S05_Def5_11c_IsMatchingEigenvectorOdd.lean` |
| Definition 5.12 | Matching idempotents and averaged rejection | `Defs/S05_Def5_12a_MatchingIdempotents.lean`, `Defs/S05_Def5_12b_GroupAlgebraAction.lean`, `Defs/S05_Def5_12c_AveragedHighMatchingElement.lean`, `Defs/S05_Def5_12d_TableauOperatorTrace.lean` |

## Results

| Status | Statement | Title | Lean file |
| --- | --- | --- | --- |
| proven | Lemma 5.1 | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` |
| proven | Theorem 5.2 | Young orthogonal action | `S05_Thm5_02_YoungOrthogonalAction.lean` |
| proven | Theorem 5.3 | Jucys--Murphy content action | `S05_Thm5_03_JucysMurphyContentAction.lean` |
| proven | Lemma 5.4 | Content separation and tableau connectivity | `S05_Lem5_04_ContentSeparationAndTableauConnectivity.lean` |
| proven | Lemma 5.5 | Young-basis scalar commutant | `S05_Lem5_05_YoungBasisScalarCommutant.lean` |
| proven | Lemma 5.6 | Orthogonality of Young matrix coefficients | `S05_Lem5_06_YoungMatrixCoefficientOrthogonality.lean` |
| proven | Lemma 5.7 | Young-lattice sum of squares | `S05_Lem5_07_YoungTableauSumOfSquares.lean` |
| proven | Lemma 5.8 | Regular Young-block decomposition | `S05_Lem5_08_RegularYoungBlockDecomposition.lean` |
| proven | Lemma 5.9 | Degree-one Young-block identification | `S05_Lem5_09_DegreeOneYoungBlockIdentification.lean` |
| proven | Lemma 5.10 | Signed two-box orthogonal branching | `S05_Lem5_10_SignedTwoBoxOrthogonalBranching.lean` |
| proven | Lemma 5.11 | One-box decomposition and deletion | `S05_Lem5_11_OneBoxDecompositionAndDeletion.lean` |
| proven | Lemma 5.12 | Branching dimensions and sign-pattern cardinalities | `S05_Lem5_12_BranchingDimensionsAndSignPatternCardinalities.lean` |
| proven | Lemma 5.13 | Matching subgroup eigenbasis | `S05_Lem5_13_MatchingSubgroupEigenbasis.lean` |
| proven | Lemma 5.14 | Matching Fourier projections | `S05_Lem5_14_MatchingFourierProjections.lean` |
| proven | Lemma 5.15 | Trace of one local truncation on one Young block | `S05_Lem5_15_TraceOfOneLocalTruncationOnOneYoungBlock.lean` |
| proven | Proposition 5.16 | Averaged rejection on Young blocks | `S05_Prop5_16_AveragedRejectionOnYoungBlocks.lean` |
| proven | Lemma 5.17 | Counting one more matching edge | `S05_Lem5_17_CountingOneMoreMatchingEdge.lean` |
| proven | Lemma 5.18 | Weight-zero entries are never a majority | `S05_Lem5_18_WeightZeroEntriesAreNeverAMajority.lean` |
| proven | Lemma 5.19 | Even certificate | `S05_Lem5_19_EvenCertificate.lean` |
| proven | Lemma 5.20 | Odd certificate | `S05_Lem5_20_OddCertificate.lean` |

Count: 12 definitions, 20 theorem-like statements, and 42 paper-facing files.
