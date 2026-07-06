# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`).  Remarks, examples, equations, proofs,
and Appendix A statements are not represented as Section 5 paper-facing Lean
files.

The former unnumbered tableau-preliminaries block is now split into five
numbered definitions, so Section 5 starts with Definitions 5.1--5.5 and the
first lemma is Lemma 5.6.

Section 5 statement count: 39.
Section 5 paper-facing Lean file count: 39.

The former Section 5 files for regular Young blocks and degree-one Young-block
identification were moved to Appendix A-facing files:

- `AppA_ThmA_03_RegularYoungBlockDecomposition.lean`
- `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean`

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| definition/interface | 5.1 | definition | Young diagrams and boxes | `S05_Def5_01_YoungDiagramsAndBoxes.lean` | `S05_Def5_01_YoungDiagram`, `S05_Def5_01_youngRow`, `S05_Def5_01_youngCells` | Young-diagram and cell vocabulary. |
| definition/interface | 5.2 | definition | Removable corners and one-box removals | `S05_Def5_02_RemovableCorners.lean` | `S05_Def5_02_IsYoungSubdiagram`, `S05_Def5_02_IsOneBoxChild`, `S05_Def5_02_oneBoxChildren`, `S05_Def5_02_IsRemovableRow` | Subdiagram, one-box child, and removable-row vocabulary. |
| definition/interface | 5.3 | definition | Standard Young tableaux and occupation notation | `S05_Def5_03_StandardTableaux.lean` | `S05_Def5_03_StandardYoungTableau`, `S05_Def5_03_cellOfEntry`, `S05_Def5_03_TableauMaxAt` | Standard-tableau and entry-location vocabulary. |
| definition/interface | 5.4 | definition | Tableau coordinate space | `S05_Def5_04_TableauCoordinateSpace.lean` | `S05_Def5_04_tableauDim`, `S05_Def5_04_TableauSpace`, `S05_Def5_04_tableauBasisVec` | Tableau-count dimension and coordinate-space vocabulary. |
| definition/interface | 5.5 | definition | Contents and adjacent operators | `S05_Def5_05_ContentAndAdjacentOperators.lean` | `S05_Def5_05_cellContent`, `S05_Def5_05_entryContent`, `S05_Def5_05_youngAdjacentOperator`, `S05_Def5_05_diagonalContentOperator` | Contents, adjacent swap operators, and diagonal content operators. |
| proven | 5.6 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_06_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_06_adjacentTranspositionsInYoungsBasis_coxeterModel` | Concrete tableau-coordinate Coxeter model. |
| proven | 5.7 | lemma | Diagonal content eigenspaces | `S05_Lem5_07_DiagonalContentEigenspaces.lean` | `S05_Lem5_07_tableauContentSequence_injective`, `S05_Lem5_07_diagonalContentEigenspaces` | Explicit diagonal content operators; Appendix A supplies the group-algebra identification. |
| definition/interface | 5.8 | definition | Young block | `S05_Def5_08_YoungBlock.lean` | `S05_YoungBlock`, `S05_Def5_08_SpectralBlockModelInput` | Vocabulary and spectral-block interface. |
| definition/interface | 5.9 | definition | Two-box removals | `S05_Def5_09_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | Removal predicates. |
| definition/interface | 5.10 | definition | Signed two-box removals | `S05_Def5_10_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | Signed removal predicates. |
| definition/interface | 5.11 | definition | One-box removals | `S05_Def5_11_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | One-box removal vocabulary. |
| proven | 5.12 | lemma | Two-box tableau branching | `S05_Lem5_12_TwoBoxTableauBranching.lean` | `S05_Lem5_12_iterated_deletion_tableauContentSequence`, `S05_Lem5_12_twoStepDeletionTableauxEquivChildTableaux` | Fixed two-step tableau deletion equivalence. |
| definition/interface | 5.13 | definition | One-box deletion spaces | `S05_Def5_13_OneBoxDeletionSpaces.lean` | `S05_Def5_13_OneBoxDeletionTableaux`, `S05_Def5_13_existsUnique_tableauMaxAt` | Deletion-fiber coordinate space vocabulary. |
| proven | 5.14 | lemma | One-box corner decomposition | `S05_Lem5_14_OneBoxCornerDecomposition.lean` | `S05_Lem5_14_row_form`, `S05_Lem5_14_removable_corner`, `S05_Lem5_14_tableau_unique_removable_corner` | Row form and removable-corner facts. |
| proven | 5.15 | lemma | One-box deletion is unitary | `S05_Lem5_15_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_15_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow`, `S05_Lem5_15_deletionCoordinateMap_inner` | Coordinate inner-product preservation. |
| proven | 5.16 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_16_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_16_deleteMax_tableauContentSequence`, `S05_Lem5_16_insertMax_youngAdjacentMatrixCoeff`, `S05_Lem5_16_deletionCoordinateMap_youngAdjacentOperator_intertwines`, `S05_Lem5_16_deletionCoordinateMap_diagonalContent_intertwines` | Proved for the concrete deletion-fiber coordinate model. |
| definition/interface | 5.17 | definition | Even sign-pattern multiset | `S05_Def5_17_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | Even sign-pattern counters. |
| definition/interface | 5.18 | definition | Odd sign-pattern multiset | `S05_Def5_18_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | Odd sign-pattern counter. |
| proven | 5.19 | lemma | Two-box dimension recursion | `S05_Lem5_19_TwoBoxDimensionRecursion.lean` | `S05_Lem5_19_tableauDim_twoStrip_branching_sized` | Tableau-count two-strip branching. |
| proven | 5.20 | lemma | One-box dimension recursion | `S05_Lem5_20_OneBoxDimensionRecursion.lean` | `S05_Lem5_20_tableauDim_oneBoxChildrenOdd_branching` | Tableau-count one-box branching. |
| proven | 5.21 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_21_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_21_tableauDim_twoStrip_size`, `S05_Lem5_21_tableauDim_oneBox_size` | Tableau-count size recurrences. |
| definition/interface | 5.22 | definition | Matching characters | `S05_Def5_22_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | Matching-cube character vocabulary. |
| proven | 5.23 | lemma | Matching subgroup eigenbasis | `S05_Lem5_23_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_23_canonicalMatchingCubeOperatorEven_eq_indexedProduct`, `S05_Lem5_23_matchingEdgeSign_finRange_product_eq_matchingCharacter`, `S05_Lem5_23_matchingCube_character_action_even`, `S05_Lem5_23_matchingEdgePlusProjectionEven_isPlusEigen`, `S05_Lem5_23_matchingEdgePlusProjectionEven_preserves_otherEigen`, `S05_Lem5_23_matchingSignProjectionEven_isMatchingEigenvector` | Listed concrete matching-operator and sign-projection wrappers are proved; the Specht/Pieri restriction content is bundled into the spectral-block model boundary. |
| proven | 5.24 | lemma | Local truncation on a matching character | `S05_Lem5_24_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_24_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_24_matchingLocalProjection_kills_high_matchingCharacter` | Matching-cube Fourier calculation. |
| proven | 5.25 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_25_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | Proved as an interface theorem from explicit matching-restriction input; the representation bridge is part of the spectral-block model boundary. |
| proven | 5.26 | definition | Matching idempotents | `S05_Def5_26_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent`, `S05_matchingLowIdempotent_idempotent`, `S05_matchingHighIdempotent_idempotent`, `S05_matchingLow_add_matchingHigh` | Low/high idempotent vocabulary plus complementary idempotence proofs. |
| proven | 5.27 | lemma | Local truncation as convolution | `S05_Lem5_27_LocalTruncationAsConvolution.lean` | `S05_Lem5_27_local_truncation_as_convolution` | Local projection as low convolution and residual as high convolution. |
| proven | 5.28 | lemma | Central averaged rejection | `S05_Lem5_28_CentralAveragedRejection.lean` | `S05_Lem5_28_matchingMeanProjectionError_eq_average`, `S05_Lem5_28_matchingMeanProjectionError_eq_high_idempotent_average` | Listed finite-average and high-idempotent norm identities are proved; Young-block centrality is part of the spectral-block model boundary. |
| proven | 5.29 | lemma | Young-basis scalar commutant | `S05_Lem5_29_YoungBasisScalarCommutant.lean` | `S05_Lem5_29_YoungBasisScalarCommutantInput`, `S05_Lem5_29_matchingAverageScalarity_eq_sum` | Scalar commutant interface and weighted-sum consequence are proved as stated in Lean. |
| proven | 5.30 | lemma | Block scalar of the averaged rejection | `S05_Lem5_30_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_30_scalar_eq_trace_div_dimension`, `S05_Lem5_30_even_scalar_eq_hEven_div_dim` | Trace-divided-by-dimension algebra is proved from the explicit scalarity and trace identity inputs. |
| proven | 5.31 | lemma | Block lower bound implies the gap | `S05_Lem5_31_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_31_spectralGapFromBlockScalars`, `S05_Lem5_31_spectralGapFromBlockTraceModel`, `S05_Lem5_31_spectralGapFromBlockModelWithDim` | Weighted-sum spectral-gap algebra. |
| proven | 5.32 | lemma | Even spectral bridge | `S05_Lem5_32_EvenSpectralBridge.lean` | `S05_Lem5_32_tableauDim_evenSpectralGapFromCertificates` | Algebraic bridge proved from explicit `SpectralBlockModelInputWithDim` hypothesis; Appendix A supplies `spectralBlockModelInputWithDim_even_from_appendixA` for the paper application. |
| proven | 5.33 | lemma | Odd spectral bridge | `S05_Lem5_33_OddSpectralBridge.lean` | `S05_Lem5_33_tableauDim_oddSpectralGapFromCertificates` | Algebraic bridge proved from explicit `SpectralBlockModelInputWithDim` hypothesis; Appendix A supplies `spectralBlockModelInputWithDim_odd_from_appendixA` for the paper application. |
| proven | 5.34 | lemma | Counting one more matching edge | `S05_Lem5_34_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_34_counting_one_more_matching_edge`, `L5_3_CountingOneMoreMatchingEdge` | Finite counting lemma. |
| proven | 5.35 | lemma | Weight-zero entries are never a majority | `S05_Lem5_35_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_35_tableau_weightZeroEntries_never_majority` | Tableau-count z-bound certificate. |
| proven | 5.36 | lemma | Where the induction can fail | `S05_Lem5_36_WhereTheInductionCanFail.lean` | `S05_Lem5_36_where_the_induction_can_fail` | Exceptional-shape localization. |
| proven | 5.37 | lemma | Even certificate | `S05_Lem5_37_EvenCertificate.lean` | `S05_Lem5_37_tableau_even_certificate` | Tableau-count even certificate. |
| proven | 5.38 | lemma | Odd exceptional children | `S05_Lem5_38_OddExceptionalChildren.lean` | `S05_Lem5_38_odd_exceptional_children` | Odd exceptional child analysis. |
| proven | 5.39 | lemma | Odd certificate | `S05_Lem5_39_OddCertificate.lean` | `S05_Lem5_39_tableau_odd_certificate` | Tableau-count odd certificate. |

Notes:

- `proven` means the Lean file proves the stated coordinate/combinatorial
  wrapper without new external assumptions.
- `definition/interface` means the file introduces vocabulary used later.
- `external: ...` rows name the representation-theoretic input being used.
- `unproven` rows name the precise missing internal or representation-layer
  component.
