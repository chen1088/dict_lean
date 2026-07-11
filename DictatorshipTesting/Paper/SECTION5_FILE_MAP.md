# Section 5 File Map

The compiled paper has separate definition and theorem-like counters.

## Definitions

| Statement | Title | Lean file(s) |
| --- | --- | --- |
| Definition 5.1 | Young diagrams and boxes | `Defs/S05_Def5_01_YoungDiagramsAndBoxes.lean` |
| Definition 5.2 | Removable corners and one-box removals | `Defs/S05_Def5_02_RemovableCorners.lean` |
| Definition 5.3 | Standard Young tableaux | `Defs/S05_Def5_03_StandardTableaux.lean` |
| Definition 5.4 | Tableau coordinate space | `Defs/S05_Def5_04_TableauCoordinateSpace.lean` |
| Definition 5.5 | Contents and adjacent operators | `Defs/S05_Def5_05_ContentAndAdjacentOperators.lean` |
| Definition 5.6 | Young matrix coefficients, blocks, and energies | `Defs/S05_Def5_06a_YoungBlock.lean`, `Defs/S05_Def5_06b_YoungMatrixCoefficients.lean`, `Defs/S05_Def5_06c_YoungBlockComponentsAndEnergies.lean` |
| Definition 5.7 | Branching data | `Defs/S05_Def5_07a_TwoBoxRemovals.lean`, `Defs/S05_Def5_07b_SignedTwoBoxRemovals.lean`, `Defs/S05_Def5_07c_OneBoxRemovals.lean` |
| Definition 5.8 | Signed two-box extension spaces | `Defs/S05_Def5_08_SignedTwoBoxExtensionSpaces.lean` |
| Definition 5.9 | One-box deletion spaces | `Defs/S05_Def5_09_OneBoxDeletionSpaces.lean` |
| Definition 5.10 | Matching sign-pattern multisets and heights | `Defs/S05_Def5_10a_EvenSignPatternMultiset.lean`, `Defs/S05_Def5_10b_OddSignPatternMultiset.lean` |
| Definition 5.11 | Matching characters and eigenvectors | `Defs/S05_Def5_11a_MatchingCharacters.lean`, `Defs/S05_Def5_11b_IsMatchingEigenvectorEven.lean`, `Defs/S05_Def5_11c_IsMatchingEigenvectorOdd.lean` |
| Definition 5.12 | Matching idempotents and averaged rejection | `Defs/S05_Def5_12a_MatchingIdempotents.lean`, `Defs/S05_Def5_12b_GroupAlgebraAction.lean`, `Defs/S05_Def5_12c_AveragedHighMatchingElement.lean`, `Defs/S05_Def5_12d_TableauOperatorTrace.lean` |
| Definition 5.13 | Certificate vocabulary | `Defs/S05_Def5_13a_CertificateSpecialDiagrams.lean`, `Defs/S05_Def5_13b_CertificateExceptionalPredicates.lean` |

## Results

| Status | Statement | Title | Lean file |
| --- | --- | --- | --- |
| proven | Lemma 5.1 | Tableau Coxeter model | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` |
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
| proven | Lemma 5.14 | One-box corner decomposition | `S05_Lem5_14_OneBoxCornerDecomposition.lean` |
| proven | Lemma 5.15 | One-box deletion is unitary | `S05_Lem5_15_OneBoxDeletionIsUnitary.lean` |
| proven | Lemma 5.16 | One-box deletion intertwines earlier swaps | `S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps.lean` |
| proven | Lemma 5.17 | Two-box dimension recursion | `S05_Lem5_17_TwoBoxDimensionRecursion.lean` |
| proven | Lemma 5.18 | One-box dimension recursion | `S05_Lem5_18_OneBoxDimensionRecursion.lean` |
| proven | Lemma 5.19 | Sizes of sign-pattern multisets | `S05_Lem5_19_SizesOfTheSignPatternMultisets.lean` |
| proven | Lemma 5.20 | Matching subgroup eigenbasis | `S05_Lem5_20_MatchingSubgroupEigenbasis.lean` |
| proven | Lemma 5.21 | Local truncation on a matching character | `S05_Lem5_21_LocalTruncationOnAMatchingCharacter.lean` |
| proven | Lemma 5.22 | Trace of one local truncation | `S05_Lem5_22_TraceOfOneLocalTruncationOnOneYoungBlock.lean` |
| proven | Lemma 5.23 | Local truncation as convolution | `S05_Lem5_23_LocalTruncationAsConvolution.lean` |
| proven | Lemma 5.24 | Central averaged rejection | `S05_Lem5_24_CentralAveragedRejection.lean` |
| proven | Lemma 5.25 | Block scalar of averaged rejection | `S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean` |
| proven | Lemma 5.26 | Global weighted matching identity | `S05_Lem5_26_GlobalWeightedMatchingIdentity.lean` |
| proven | Lemma 5.27 | Block lower bound implies the gap | `S05_Lem5_27_BlockLowerBoundImpliesTheGap.lean` |
| proven | Lemma 5.28 | Even spectral bridge | `S05_Lem5_28_EvenSpectralBridge.lean` |
| proven | Lemma 5.29 | Odd spectral bridge | `S05_Lem5_29_OddSpectralBridge.lean` |
| proven | Lemma 5.30 | Counting one more matching edge | `S05_Lem5_30_CountingOneMoreMatchingEdge.lean` |
| proven | Lemma 5.31 | Weight-zero entries are never a majority | `S05_Lem5_31_WeightZeroEntriesAreNeverAMajority.lean` |
| proven | Lemma 5.32 | Where the induction can fail | `S05_Lem5_32_WhereTheInductionCanFail.lean` |
| proven | Lemma 5.33 | Even certificate | `S05_Lem5_33_EvenCertificate.lean` |
| proven | Lemma 5.34 | Odd exceptional children | `S05_Lem5_34_OddExceptionalChildren.lean` |
| proven | Lemma 5.35 | Odd certificate | `S05_Lem5_35_OddCertificate.lean` |

Count: 13 definitions, 35 theorem-like statements, and 59 paper-facing files.
