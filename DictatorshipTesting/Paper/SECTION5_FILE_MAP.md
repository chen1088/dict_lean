# Section 5 File Map

The compiled paper has separate definition and theorem-like counters.

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
| proven | Lemma 5.2 | Type-A adjacent-word presentation | `S05_Lem5_02_TypeAAdjacentWordPresentation.lean` |
| proven | Theorem 5.3 | Young orthogonal action | `S05_Thm5_03_YoungOrthogonalAction.lean` |
| proven | Lemma 5.4 | Jucys--Murphy recurrences | `S05_Lem5_04_JucysMurphyRecurrences.lean` |
| proven | Theorem 5.5 | Jucys--Murphy content action | `S05_Thm5_05_JucysMurphyContentAction.lean` |
| proven | Lemma 5.6 | Diagonal content eigenspaces | `S05_Lem5_06_DiagonalContentEigenspaces.lean` |
| proven | Lemma 5.7 | Connectedness of standard tableaux | `S05_Lem5_07_ConnectednessOfStandardTableaux.lean` |
| proven | Lemma 5.8 | Young-basis scalar commutant | `S05_Lem5_08_YoungBasisScalarCommutant.lean` |
| proven | Lemma 5.9 | Orthogonality of Young matrix coefficients | `S05_Lem5_09_YoungMatrixCoefficientOrthogonality.lean` |
| proven | Lemma 5.10 | Young-lattice sum of squares | `S05_Lem5_10_YoungTableauSumOfSquares.lean` |
| proven | Lemma 5.11 | Regular Young-block decomposition | `S05_Lem5_11_RegularYoungBlockDecomposition.lean` |
| proven | Lemma 5.12 | Degree-one Young-block identification | `S05_Lem5_12_DegreeOneYoungBlockIdentification.lean` |
| proven | Lemma 5.13 | Signed two-box orthogonal branching | `S05_Lem5_13_SignedTwoBoxOrthogonalBranching.lean` |
| proven | Lemma 5.14 | One-box decomposition and deletion | `S05_Lem5_14_OneBoxDecompositionAndDeletion.lean` |
| proven | Lemma 5.15 | Branching dimensions and sign-pattern cardinalities | `S05_Lem5_15_BranchingDimensionsAndSignPatternCardinalities.lean` |
| proven | Lemma 5.16 | Matching subgroup eigenbasis | `S05_Lem5_16_MatchingSubgroupEigenbasis.lean` |
| proven | Lemma 5.17 | Local truncation on a matching character | `S05_Lem5_17_LocalTruncationOnAMatchingCharacter.lean` |
| proven | Lemma 5.18 | Trace of one local truncation on one Young block | `S05_Lem5_18_TraceOfOneLocalTruncationOnOneYoungBlock.lean` |
| proven | Lemma 5.19 | Local truncation as convolution | `S05_Lem5_19_LocalTruncationAsConvolution.lean` |
| proven | Lemma 5.20 | Central averaged rejection | `S05_Lem5_20_CentralAveragedRejection.lean` |
| proven | Lemma 5.21 | Block scalar of the averaged rejection | `S05_Lem5_21_BlockScalarOfTheAveragedRejection.lean` |
| proven | Lemma 5.22 | Global weighted matching identity | `S05_Lem5_22_GlobalWeightedMatchingIdentity.lean` |
| proven | Lemma 5.23 | Counting one more matching edge | `S05_Lem5_23_CountingOneMoreMatchingEdge.lean` |
| proven | Lemma 5.24 | Weight-zero entries are never a majority | `S05_Lem5_24_WeightZeroEntriesAreNeverAMajority.lean` |
| proven | Lemma 5.25 | Even certificate | `S05_Lem5_25_EvenCertificate.lean` |
| proven | Lemma 5.26 | Odd certificate | `S05_Lem5_26_OddCertificate.lean` |

Count: 12 definitions, 26 theorem-like statements, and 48 paper-facing files.
