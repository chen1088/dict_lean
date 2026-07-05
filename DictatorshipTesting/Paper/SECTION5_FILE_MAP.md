# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`).  Remarks, examples, equations, proofs,
and Appendix A statements are not represented as Section 5 paper-facing Lean
files.

Section 5 statement count: 34.
Section 5 paper-facing Lean file count: 34.

The former Section 5 files for regular Young blocks and degree-one Young-block
identification were moved to Appendix A-facing files:

- `AppA_ThmA_03_RegularYoungBlockDecomposition.lean`
- `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean`

| Paper stmt | Environment | Paper title | Lean file | Main wrappers | Status |
| --- | --- | --- | --- | --- | --- |
| 5.1 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel` | proved |
| 5.2 | lemma | Diagonal content eigenspaces | `S05_Lem5_02_DiagonalContentEigenspaces.lean` | `S05_Lem5_02_tableauContentSequence_injective`, `S05_Lem5_02_diagonalContentEigenspaces` | proved |
| 5.3 | definition | Young block | `S05_Def5_03_YoungBlock.lean` | `S05_YoungBlock`, `S05_Def5_03_SpectralBlockModelInput` | definition/interface |
| 5.4 | definition | Two-box removals | `S05_Def5_04_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | definition/interface |
| 5.5 | definition | Signed two-box removals | `S05_Def5_05_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | definition/interface |
| 5.6 | definition | One-box removals | `S05_Def5_06_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | definition/interface |
| 5.7 | lemma | Two-box tableau branching | `S05_Lem5_07_TwoBoxTableauBranching.lean` | `S05_Lem5_07_iterated_deletion_tableauContentSequence`, `S05_Lem5_07_twoStepDeletionTableauxEquivChildTableaux` | proved |
| 5.8 | definition | One-box deletion spaces | `S05_Def5_08_OneBoxDeletionSpaces.lean` | `S05_Def5_08_OneBoxDeletionTableaux`, `S05_Def5_08_existsUnique_tableauMaxAt` | definition/interface |
| 5.9 | lemma | One-box corner decomposition | `S05_Lem5_09_OneBoxCornerDecomposition.lean` | `S05_Lem5_09_row_form`, `S05_Lem5_09_removable_corner`, `S05_Lem5_09_tableau_unique_removable_corner` | proved |
| 5.10 | lemma | One-box deletion is unitary | `S05_Lem5_10_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_10_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow`, `S05_Lem5_10_deletionCoordinateMap_inner` | proved |
| 5.11 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_11_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_11_deleteMax_tableauContentSequence`, `S05_Lem5_11_insertMax_youngAdjacentDiagCoeff`, `S05_Lem5_11_insertMax_youngAdjacentOffCoeff`, `S05_Lem5_11_deletionCoordinateMap_diagonalContent_intertwines` | partially proven: surviving content and earlier adjacent row/column/coefficient preservation are proved; full coordinate-level Young-adjacent-operator intertwining still missing |
| 5.12 | definition | Even sign-pattern multiset | `S05_Def5_12_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | definition/interface |
| 5.13 | definition | Odd sign-pattern multiset | `S05_Def5_13_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | definition/interface |
| 5.14 | lemma | Two-box dimension recursion | `S05_Lem5_14_TwoBoxDimensionRecursion.lean` | `S05_Lem5_14_tableauDim_twoStrip_branching_sized` | proved |
| 5.15 | lemma | One-box dimension recursion | `S05_Lem5_15_OneBoxDimensionRecursion.lean` | `S05_Lem5_15_tableauDim_oneBoxChildrenOdd_branching` | proved |
| 5.16 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_16_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_16_tableauDim_twoStrip_size`, `S05_Lem5_16_tableauDim_oneBox_size` | proved |
| 5.17 | definition | Matching characters | `S05_Def5_17_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | definition/interface |
| 5.18 | lemma | Matching subgroup eigenbasis | `S05_Lem5_18_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_18_canonicalMatchingCubeOperatorEven_eq_indexedProduct`, `S05_Lem5_18_matchingEdgeSign_finRange_product_eq_matchingCharacter`, `S05_Lem5_18_matchingCube_character_action_even`, `S05_Lem5_18_matchingEdgePlusProjectionEven_isPlusEigen` | external: Specht matching-restriction theorem |
| 5.19 | lemma | Local truncation on a matching character | `S05_Lem5_19_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_19_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_19_matchingLocalProjection_kills_high_matchingCharacter` | proved |
| 5.20 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_20_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | external: matching-character restriction data |
| 5.21 | definition | Matching idempotents | `S05_Def5_21_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent` | definition/interface |
| 5.22 | lemma | Local truncation as convolution | `S05_Lem5_22_LocalTruncationAsConvolution.lean` | `S05_Lem5_22_local_truncation_as_convolution` | proved |
| 5.23 | lemma | Central averaged rejection | `S05_Lem5_23_CentralAveragedRejection.lean` | `S05_Lem5_23_matchingMeanProjectionError_eq_average`, `S05_Lem5_23_matchingMeanProjectionError_eq_high_idempotent_average` | external: Appendix A Young-block/Schur scalarity input |
| 5.24 | lemma | Young-basis scalar commutant | `S05_Lem5_24_YoungBasisScalarCommutant.lean` | `S05_Lem5_24_YoungBasisScalarCommutantInput`, `S05_Lem5_24_matchingAverageScalarity_eq_sum` | external: Appendix A Young-block/Schur scalarity input |
| 5.25 | lemma | Block scalar of the averaged rejection | `S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_25_scalar_eq_trace_div_dimension`, `S05_Lem5_25_even_scalar_eq_hEven_div_dim` | external: scalarity and trace identity inputs |
| 5.26 | lemma | Block lower bound implies the gap | `S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_26_spectralGapFromBlockScalars`, `S05_Lem5_26_spectralGapFromBlockTraceModel`, `S05_Lem5_26_spectralGapFromBlockModelWithDim` | proved |
| 5.27 | lemma | Even spectral bridge | `S05_Lem5_27_EvenSpectralBridge.lean` | `S05_Lem5_27_tableauDim_evenSpectralGapFromCertificates` | unproven: needs SpectralBlockModelInputWithDim for tableauDim/hEvenTableau |
| 5.28 | lemma | Odd spectral bridge | `S05_Lem5_28_OddSpectralBridge.lean` | `S05_Lem5_28_tableauDim_oddSpectralGapFromCertificates` | unproven: needs SpectralBlockModelInputWithDim for tableauDim/hOddTableau |
| 5.29 | lemma | Counting one more matching edge | `S05_Lem5_29_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_29_counting_one_more_matching_edge`, `L5_3_CountingOneMoreMatchingEdge` | proved |
| 5.30 | lemma | Weight-zero entries are never a majority | `S05_Lem5_30_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_30_tableau_weightZeroEntries_never_majority` | proved |
| 5.31 | lemma | Where the induction can fail | `S05_Lem5_31_WhereTheInductionCanFail.lean` | `S05_Lem5_31_where_the_induction_can_fail` | proved |
| 5.32 | lemma | Even certificate | `S05_Lem5_32_EvenCertificate.lean` | `S05_Lem5_32_tableau_even_certificate` | proved |
| 5.33 | lemma | Odd exceptional children | `S05_Lem5_33_OddExceptionalChildren.lean` | `S05_Lem5_33_odd_exceptional_children` | proved |
| 5.34 | lemma | Odd certificate | `S05_Lem5_34_OddCertificate.lean` | `S05_Lem5_34_tableau_odd_certificate` | proved |

Notes:

- `proved` means the Lean file proves the stated coordinate/combinatorial
  wrapper without new external assumptions.
- `definition/interface` means the file introduces vocabulary used later.
- `external` rows name the representation-theoretic input being used.
- `unproven` rows name the precise missing internal or representation-layer
  component.
