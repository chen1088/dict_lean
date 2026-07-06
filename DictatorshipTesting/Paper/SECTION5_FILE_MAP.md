# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`).  Remarks, examples, equations, proofs,
and Appendix A statements are not represented as Section 5 paper-facing Lean
files.

The currently unnumbered Section 5.1 tableau-preliminaries block is split in
the dependency graph into five compact interface nodes:

- `5.1 def A`: Young diagrams and boxes;
- `5.1 def B`: subdiagrams and one-box children;
- `5.1 def C`: standard tableaux and occupation notation;
- `5.1 def D`: tableau coordinate space and Young basis vectors;
- `5.1 def E`: contents, adjacent operators, and diagonal content operators.

These are presentation/interface nodes; the numbered Section 5 count below is
unchanged until the paper source is renumbered.

Section 5 statement count: 34.
Section 5 paper-facing Lean file count: 34.

The former Section 5 files for regular Young blocks and degree-one Young-block
identification were moved to Appendix A-facing files:

- `AppA_ThmA_03_RegularYoungBlockDecomposition.lean`
- `AppA_LemA_04_DegreeOneYoungBlockIdentification.lean`

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| proven | 5.1 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel` | Concrete tableau-coordinate Coxeter model. |
| proven | 5.2 | lemma | Diagonal content eigenspaces | `S05_Lem5_02_DiagonalContentEigenspaces.lean` | `S05_Lem5_02_tableauContentSequence_injective`, `S05_Lem5_02_diagonalContentEigenspaces` | Explicit diagonal content operators; Appendix A supplies the group-algebra identification. |
| definition/interface | 5.3 | definition | Young block | `S05_Def5_03_YoungBlock.lean` | `S05_YoungBlock`, `S05_Def5_03_SpectralBlockModelInput` | Vocabulary and spectral-block interface. |
| definition/interface | 5.4 | definition | Two-box removals | `S05_Def5_04_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | Removal predicates. |
| definition/interface | 5.5 | definition | Signed two-box removals | `S05_Def5_05_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | Signed removal predicates. |
| definition/interface | 5.6 | definition | One-box removals | `S05_Def5_06_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | One-box removal vocabulary. |
| proven | 5.7 | lemma | Two-box tableau branching | `S05_Lem5_07_TwoBoxTableauBranching.lean` | `S05_Lem5_07_iterated_deletion_tableauContentSequence`, `S05_Lem5_07_twoStepDeletionTableauxEquivChildTableaux` | Fixed two-step tableau deletion equivalence. |
| definition/interface | 5.8 | definition | One-box deletion spaces | `S05_Def5_08_OneBoxDeletionSpaces.lean` | `S05_Def5_08_OneBoxDeletionTableaux`, `S05_Def5_08_existsUnique_tableauMaxAt` | Deletion-fiber coordinate space vocabulary. |
| proven | 5.9 | lemma | One-box corner decomposition | `S05_Lem5_09_OneBoxCornerDecomposition.lean` | `S05_Lem5_09_row_form`, `S05_Lem5_09_removable_corner`, `S05_Lem5_09_tableau_unique_removable_corner` | Row form and removable-corner facts. |
| proven | 5.10 | lemma | One-box deletion is unitary | `S05_Lem5_10_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_10_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow`, `S05_Lem5_10_deletionCoordinateMap_inner` | Coordinate inner-product preservation. |
| proven | 5.11 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_11_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_11_deleteMax_tableauContentSequence`, `S05_Lem5_11_insertMax_youngAdjacentMatrixCoeff`, `S05_Lem5_11_deletionCoordinateMap_youngAdjacentOperator_intertwines`, `S05_Lem5_11_deletionCoordinateMap_diagonalContent_intertwines` | Proved for the concrete deletion-fiber coordinate model. |
| definition/interface | 5.12 | definition | Even sign-pattern multiset | `S05_Def5_12_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | Even sign-pattern counters. |
| definition/interface | 5.13 | definition | Odd sign-pattern multiset | `S05_Def5_13_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | Odd sign-pattern counter. |
| proven | 5.14 | lemma | Two-box dimension recursion | `S05_Lem5_14_TwoBoxDimensionRecursion.lean` | `S05_Lem5_14_tableauDim_twoStrip_branching_sized` | Tableau-count two-strip branching. |
| proven | 5.15 | lemma | One-box dimension recursion | `S05_Lem5_15_OneBoxDimensionRecursion.lean` | `S05_Lem5_15_tableauDim_oneBoxChildrenOdd_branching` | Tableau-count one-box branching. |
| proven | 5.16 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_16_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_16_tableauDim_twoStrip_size`, `S05_Lem5_16_tableauDim_oneBox_size` | Tableau-count size recurrences. |
| definition/interface | 5.17 | definition | Matching characters | `S05_Def5_17_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | Matching-cube character vocabulary. |
| proven | 5.18 | lemma | Matching subgroup eigenbasis | `S05_Lem5_18_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_18_canonicalMatchingCubeOperatorEven_eq_indexedProduct`, `S05_Lem5_18_matchingEdgeSign_finRange_product_eq_matchingCharacter`, `S05_Lem5_18_matchingCube_character_action_even`, `S05_Lem5_18_matchingEdgePlusProjectionEven_isPlusEigen`, `S05_Lem5_18_matchingEdgePlusProjectionEven_preserves_otherEigen`, `S05_Lem5_18_matchingSignProjectionEven_isMatchingEigenvector` | Listed concrete matching-operator and sign-projection wrappers are proved; the Specht/Pieri restriction content is bundled into the spectral-block model boundary. |
| proven | 5.19 | lemma | Local truncation on a matching character | `S05_Lem5_19_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_19_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_19_matchingLocalProjection_kills_high_matchingCharacter` | Matching-cube Fourier calculation. |
| proven | 5.20 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_20_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | Proved as an interface theorem from explicit matching-restriction input; the representation bridge is part of the spectral-block model boundary. |
| proven | 5.21 | definition | Matching idempotents | `S05_Def5_21_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent`, `S05_matchingLowIdempotent_idempotent`, `S05_matchingHighIdempotent_idempotent`, `S05_matchingLow_add_matchingHigh` | Low/high idempotent vocabulary plus complementary idempotence proofs. |
| proven | 5.22 | lemma | Local truncation as convolution | `S05_Lem5_22_LocalTruncationAsConvolution.lean` | `S05_Lem5_22_local_truncation_as_convolution` | Local projection as low convolution and residual as high convolution. |
| proven | 5.23 | lemma | Central averaged rejection | `S05_Lem5_23_CentralAveragedRejection.lean` | `S05_Lem5_23_matchingMeanProjectionError_eq_average`, `S05_Lem5_23_matchingMeanProjectionError_eq_high_idempotent_average` | Listed finite-average and high-idempotent norm identities are proved; Young-block centrality is part of the spectral-block model boundary. |
| proven | 5.24 | lemma | Young-basis scalar commutant | `S05_Lem5_24_YoungBasisScalarCommutant.lean` | `S05_Lem5_24_YoungBasisScalarCommutantInput`, `S05_Lem5_24_matchingAverageScalarity_eq_sum` | Scalar commutant interface and weighted-sum consequence are proved as stated in Lean. |
| proven | 5.25 | lemma | Block scalar of the averaged rejection | `S05_Lem5_25_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_25_scalar_eq_trace_div_dimension`, `S05_Lem5_25_even_scalar_eq_hEven_div_dim` | Trace-divided-by-dimension algebra is proved from the explicit scalarity and trace identity inputs. |
| proven | 5.26 | lemma | Block lower bound implies the gap | `S05_Lem5_26_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_26_spectralGapFromBlockScalars`, `S05_Lem5_26_spectralGapFromBlockTraceModel`, `S05_Lem5_26_spectralGapFromBlockModelWithDim` | Weighted-sum spectral-gap algebra. |
| proven | 5.27 | lemma | Even spectral bridge | `S05_Lem5_27_EvenSpectralBridge.lean` | `S05_Lem5_27_tableauDim_evenSpectralGapFromCertificates` | Algebraic bridge proved from explicit `SpectralBlockModelInputWithDim` hypothesis; Appendix A supplies `spectralBlockModelInputWithDim_even_from_appendixA` for the paper application. |
| proven | 5.28 | lemma | Odd spectral bridge | `S05_Lem5_28_OddSpectralBridge.lean` | `S05_Lem5_28_tableauDim_oddSpectralGapFromCertificates` | Algebraic bridge proved from explicit `SpectralBlockModelInputWithDim` hypothesis; Appendix A supplies `spectralBlockModelInputWithDim_odd_from_appendixA` for the paper application. |
| proven | 5.29 | lemma | Counting one more matching edge | `S05_Lem5_29_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_29_counting_one_more_matching_edge`, `L5_3_CountingOneMoreMatchingEdge` | Finite counting lemma. |
| proven | 5.30 | lemma | Weight-zero entries are never a majority | `S05_Lem5_30_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_30_tableau_weightZeroEntries_never_majority` | Tableau-count z-bound certificate. |
| proven | 5.31 | lemma | Where the induction can fail | `S05_Lem5_31_WhereTheInductionCanFail.lean` | `S05_Lem5_31_where_the_induction_can_fail` | Exceptional-shape localization. |
| proven | 5.32 | lemma | Even certificate | `S05_Lem5_32_EvenCertificate.lean` | `S05_Lem5_32_tableau_even_certificate` | Tableau-count even certificate. |
| proven | 5.33 | lemma | Odd exceptional children | `S05_Lem5_33_OddExceptionalChildren.lean` | `S05_Lem5_33_odd_exceptional_children` | Odd exceptional child analysis. |
| proven | 5.34 | lemma | Odd certificate | `S05_Lem5_34_OddCertificate.lean` | `S05_Lem5_34_tableau_odd_certificate` | Tableau-count odd certificate. |

Notes:

- `proven` means the Lean file proves the stated coordinate/combinatorial
  wrapper without new external assumptions.
- `definition/interface` means the file introduces vocabulary used later.
- `external: ...` rows name the representation-theoretic input being used.
- `unproven` rows name the precise missing internal or representation-layer
  component.
