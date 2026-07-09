# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: theorem-like numbered environments only (`definition`, `lemma`,
`proposition`, `theorem`, `corollary`).  Remarks, examples, equations, proofs,
and Appendix A statements are not represented as Section 5 paper-facing Lean
files.

Section 5 statement count: 49.
Section 5 paper-facing Lean file count: 49.

The former unnumbered tableau-preliminaries block is split into numbered
Definitions 5.1--5.5.  Interface definitions that were formerly bundled into
larger lemmas now have their own numbers, so no two Section 5 paper-facing Lean
files share the same statement number.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| definition/interface | 5.1 | definition | Young diagrams and boxes | `S05_Def5_01_YoungDiagramsAndBoxes.lean` | `S05_Def5_01_YoungDiagram`, `S05_Def5_01_youngRow`, `S05_Def5_01_youngCells` | Young-diagram and cell vocabulary. |
| definition/interface | 5.2 | definition | Removable corners and one-box removals | `S05_Def5_02_RemovableCorners.lean` | `S05_Def5_02_IsYoungSubdiagram`, `S05_Def5_02_IsOneBoxChild`, `S05_Def5_02_oneBoxChildren`, `S05_Def5_02_IsRemovableRow` | Subdiagram, one-box child, and removable-row vocabulary. |
| definition/interface | 5.3 | definition | Standard Young tableaux and occupation notation | `S05_Def5_03_StandardTableaux.lean` | `S05_Def5_03_StandardYoungTableau`, `S05_Def5_03_cellOfEntry`, `S05_Def5_03_TableauMaxAt` | Standard-tableau and entry-location vocabulary. |
| definition/interface | 5.4 | definition | Tableau coordinate space | `S05_Def5_04_TableauCoordinateSpace.lean` | `S05_Def5_04_tableauDim`, `S05_Def5_04_TableauSpace`, `S05_Def5_04_tableauBasisVec` | Tableau-count dimension and coordinate-space vocabulary. |
| definition/interface | 5.5 | definition | Contents and adjacent operators | `S05_Def5_05_ContentAndAdjacentOperators.lean` | `S05_Def5_05_cellContent`, `S05_Def5_05_entryContent`, `S05_Def5_05_youngAdjacentOperator`, `S05_Def5_05_diagonalContentOperator` | Contents, adjacent swap operators, and diagonal content operators. |
| proven | 5.6 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_06_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_06_adjacentTranspositionsInYoungsBasis_coxeterModel` | Concrete tableau-coordinate Coxeter model. |
| proven | 5.7 | lemma | Diagonal content eigenspaces | `S05_Lem5_07_DiagonalContentEigenspaces.lean` | `S05_Lem5_07_tableauContentSequence_injective`, `S05_Lem5_07_diagonalContentEigenspaces` | Explicit diagonal content operators; Appendix A supplies the group-algebra identification. |
| definition/interface | 5.8 | definition | Young block | `S05_Def5_08_YoungBlock.lean` | `S05_YoungBlock` | Young-block index vocabulary. |
| definition/interface | 5.9 | definition | Young-block energy profile | `S05_Def5_09_YoungBlockDecompositionInput.lean` | `S05_Def5_09_YoungBlockDecompositionInput` | Nonnegative numerical block-energy profile interface. |
| definition/interface | 5.10 | definition | U1-compatible Young-block profile | `S05_Def5_10_U1YoungBlockIdentificationInput.lean` | `S05_Def5_10_U1YoungBlockIdentificationInput` | Numerical interface identifying the one-row and standard blocks with `U_1`. |
| definition/interface | 5.11 | definition | Two-box removals | `S05_Def5_11_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | Horizontal and vertical two-box removal predicates. |
| definition/interface | 5.12 | definition | Signed two-box removals | `S05_Def5_12_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | Signed removal predicates. |
| definition/interface | 5.13 | definition | One-box removals | `S05_Def5_13_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | One-box removal vocabulary. |
| proven | 5.14 | lemma | Two-box tableau branching | `S05_Lem5_14_TwoBoxTableauBranching.lean` | `S05_Lem5_14_iterated_deletion_tableauContentSequence`, `S05_Lem5_14_twoStepDeletionTableauxEquivChildTableaux` | Fixed two-step tableau deletion equivalence. |
| definition/interface | 5.15 | definition | One-box deletion spaces | `S05_Def5_15_OneBoxDeletionSpaces.lean` | `S05_Def5_15_OneBoxDeletionTableaux`, `S05_Def5_15_existsUnique_tableauMaxAt` | Deletion-fiber coordinate space vocabulary. |
| proven | 5.16 | lemma | One-box corner decomposition | `S05_Lem5_16_OneBoxCornerDecomposition.lean` | `S05_Lem5_16_row_form`, `S05_Lem5_16_removable_corner`, `S05_Lem5_16_tableau_unique_removable_corner` | Row form and removable-corner facts. |
| proven | 5.17 | lemma | One-box deletion is unitary | `S05_Lem5_17_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_17_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow`, `S05_Lem5_17_deletionCoordinateMap_inner` | Coordinate inner-product preservation. |
| proven | 5.18 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_18_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_18_deletionCoordinateMap_youngAdjacentOperator_intertwines`, `S05_Lem5_18_deletionCoordinateMap_diagonalContent_intertwines` | Coordinate-level intertwining for deletion fibers. |
| definition/interface | 5.19 | definition | Even sign-pattern multiset | `S05_Def5_19_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | Even sign-pattern counters. |
| definition/interface | 5.20 | definition | Odd sign-pattern multiset | `S05_Def5_20_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | Odd sign-pattern counter. |
| proven | 5.21 | lemma | Two-box dimension recursion | `S05_Lem5_21_TwoBoxDimensionRecursion.lean` | `S05_Lem5_21_tableauDim_twoStrip_branching_sized` | Tableau-count two-strip branching. |
| proven | 5.22 | lemma | One-box dimension recursion | `S05_Lem5_22_OneBoxDimensionRecursion.lean` | `S05_Lem5_22_tableauDim_oneBoxChildrenOdd_branching` | Tableau-count one-box branching. |
| proven | 5.23 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_23_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_23_tableauDim_twoStrip_size`, `S05_Lem5_23_tableauDim_oneBox_size` | Tableau-count size recurrences. |
| definition/interface | 5.24 | definition | Matching characters | `S05_Def5_24_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | Matching-cube character vocabulary. |
| definition/interface | 5.25 | definition | Even matching eigenvector predicate | `S05_Def5_25_IsMatchingEigenvectorEven.lean` | `S05_IsMatchingEigenvectorEven` | Simultaneous even matching-edge eigenvector predicate. |
| definition/interface | 5.26 | definition | Odd matching eigenvector predicate | `S05_Def5_26_IsMatchingEigenvectorOdd.lean` | `S05_IsMatchingEigenvectorOdd` | Simultaneous odd matching-edge eigenvector predicate. |
| definition/interface | 5.27 | definition | Even matching-restriction scalar input | `S05_Def5_27_MatchingRestrictionEvenInput.lean` | `MatchingRestrictionEvenInput` | Even scalar input extracted from matching restriction. |
| definition/interface | 5.28 | definition | Odd matching-restriction scalar input | `S05_Def5_28_MatchingRestrictionOddInput.lean` | `MatchingRestrictionOddInput` | Odd scalar input extracted from matching restriction. |
| proven | 5.29 | lemma | Matching subgroup eigenbasis | `S05_Lem5_29_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_29_matchingSignProjectionEven_isMatchingEigenvector`, `S05_Lem5_29_matchingSignProjectionOdd_isMatchingEigenvector` | Concrete matching-operator and sign-projection wrappers are proved; Specht/Pieri restriction content is bundled into the spectral-block model boundary. |
| proven | 5.30 | lemma | Local truncation on a matching character | `S05_Lem5_30_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_30_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_30_matchingLocalProjection_kills_high_matchingCharacter` | Matching-cube Fourier calculation. |
| definition/interface | 5.31 | definition | Even local-truncation trace input | `S05_Def5_31_TraceLocalTruncationEvenInput.lean` | `TraceLocalTruncationEvenInput` | Scalar trace formula interface for one even Young block. |
| definition/interface | 5.32 | definition | Odd local-truncation trace input | `S05_Def5_32_TraceLocalTruncationOddInput.lean` | `TraceLocalTruncationOddInput` | Scalar trace formula interface for one odd Young block. |
| external: block trace model input | 5.33 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_33_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | Trace formula wrappers from explicit scalar inputs. |
| proven | 5.34 | definition | Matching idempotents | `S05_Def5_34_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent`, `S05_matchingLow_add_matchingHigh` | Low/high idempotent vocabulary plus complementary idempotence proofs. |
| proven | 5.35 | lemma | Local truncation as convolution | `S05_Lem5_35_LocalTruncationAsConvolution.lean` | `S05_Lem5_35_local_truncation_as_convolution` | Local projection as low convolution and residual as high convolution. |
| external: Young-block centrality input | 5.36 | lemma | Central averaged rejection | `S05_Lem5_36_CentralAveragedRejection.lean` | `S05_Lem5_36_matchingMeanProjectionError_eq_average`, `S05_Lem5_36_matchingMeanProjectionError_eq_high_idempotent_average` | Finite-average and high-idempotent norm identities are proved; centrality on Young blocks is part of the spectral-block model boundary. |
| definition/interface | 5.37 | definition | Young-basis scalar commutant input | `S05_Def5_37_YoungBasisScalarCommutantInput.lean` | `S05_Def5_37_YoungBasisScalarCommutantInput` | Scalarity interface consumed by the spectral bridge. |
| external: scalar commutant input | 5.38 | lemma | Young-basis scalar commutant | `S05_Lem5_38_YoungBasisScalarCommutant.lean` | `S05_Lem5_38_matchingAverageScalarity_eq_sum` | Projection from the explicit scalarity input to the weighted-sum identity. |
| external: trace/scalar model input | 5.39 | lemma | Block scalar of the averaged rejection | `S05_Lem5_39_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_39_scalar_eq_trace_div_dimension`, `S05_Lem5_39_even_scalar_eq_hEven_div_dim` | Trace-divided-by-dimension algebra from explicit scalarity and trace identities. |
| proven | 5.40 | lemma | Block lower bound implies the gap | `S05_Lem5_40_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_40_spectralGapFromBlockScalars`, `S05_Lem5_40_spectralGapFromBlockModelWithDim` | Weighted-sum spectral-gap algebra. |
| proven | 5.41 | lemma | Regular Young-block decomposition | `S05_Lem5_41_RegularYoungBlockDecomposition.lean` | `spectralBlockModelInputWithDim_even_from_appendixA`, `spectralBlockModelInputWithDim_odd_from_appendixA` | Assembly from Appendix A inputs into the `SpectralBlockModelInputWithDim` interface. |
| proven | 5.42 | lemma | Even spectral bridge | `S05_Lem5_42_EvenSpectralBridge.lean` | `S05_Lem5_42_tableauDim_evenSpectralGapFromCertificates` | Algebraic bridge from explicit `SpectralBlockModelInputWithDim` hypothesis and finite certificate. |
| proven | 5.43 | lemma | Odd spectral bridge | `S05_Lem5_43_OddSpectralBridge.lean` | `S05_Lem5_43_tableauDim_oddSpectralGapFromCertificates` | Algebraic bridge from explicit `SpectralBlockModelInputWithDim` hypothesis and finite certificate. |
| proven | 5.44 | lemma | Counting one more matching edge | `S05_Lem5_44_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_44_counting_one_more_matching_edge` | Finite counting lemma. |
| proven | 5.45 | lemma | Weight-zero entries are never a majority | `S05_Lem5_45_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_45_tableau_weightZeroEntries_never_majority` | Tableau-count z-bound certificate. |
| proven | 5.46 | lemma | Where the induction can fail | `S05_Lem5_46_WhereTheInductionCanFail.lean` | `S05_Lem5_46_where_the_induction_can_fail` | Exceptional-shape localization. |
| proven | 5.47 | lemma | Even certificate | `S05_Lem5_47_EvenCertificate.lean` | `S05_Lem5_47_tableau_even_certificate` | Tableau-count even certificate; reusable height definition is in `S05_Def_TableauEvenHeight.lean`. |
| proven | 5.48 | lemma | Odd exceptional children | `S05_Lem5_48_OddExceptionalChildren.lean` | `S05_Lem5_48_odd_exceptional_children` | Odd exceptional child analysis. |
| proven | 5.49 | lemma | Odd certificate | `S05_Lem5_49_OddCertificate.lean` | `S05_Lem5_49_tableau_odd_certificate` | Tableau-count odd certificate; reusable height definition is in `S05_Def_TableauOddHeight.lean`. |

Notes:

- `proven` means the Lean file proves the stated coordinate/combinatorial wrapper without new external assumptions.
- `definition/interface` means the file introduces vocabulary used later.
- `external: ...` rows name the representation-theoretic input being used.
- Neutral height definitions used by both Appendix A.2 and the finite certificate proofs are split into `S05_Def_TableauEvenHeight.lean` and `S05_Def_TableauOddHeight.lean`; they are not separate numbered paper theorem statements.