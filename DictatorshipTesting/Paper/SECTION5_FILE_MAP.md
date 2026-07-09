# Section 5 File Map

Source checked: `../dictatorship_testing_soda27_latest.tex`.

Counting rule: Section 5 definitions have their own `Def 5.x` counter, while
lemmas/theorems/propositions/corollaries have their own result counter.  Remarks,
examples, equations, proofs, and Appendix A statements are not represented as
Section 5 paper-facing Lean files.

Section 5 definition count: 23.
Section 5 result count: 26.
Section 5 paper-facing Lean file count: 49.

The former unnumbered tableau-preliminaries block is split into numbered
Definitions 5.1--5.5.  Interface definitions that were formerly bundled into
larger lemmas now have their own definition numbers.  The result counter starts
again at Lemma 5.1, so the table always displays the prefix `Def` or `Lem`.

| Status | Paper stmt | Environment | Paper title | Lean file | Main wrappers | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| definition/interface | Def 5.1 | definition | Young diagrams and boxes | `S05_Def5_01_YoungDiagramsAndBoxes.lean` | `S05_Def5_01_YoungDiagram`, `S05_Def5_01_youngRow`, `S05_Def5_01_youngCells` | Young-diagram and cell vocabulary. |
| definition/interface | Def 5.2 | definition | Removable corners and one-box removals | `S05_Def5_02_RemovableCorners.lean` | `S05_Def5_02_IsYoungSubdiagram`, `S05_Def5_02_IsOneBoxChild`, `S05_Def5_02_oneBoxChildren`, `S05_Def5_02_IsRemovableRow` | Subdiagram, one-box child, and removable-row vocabulary. |
| definition/interface | Def 5.3 | definition | Standard Young tableaux and occupation notation | `S05_Def5_03_StandardTableaux.lean` | `S05_Def5_03_StandardYoungTableau`, `S05_Def5_03_cellOfEntry`, `S05_Def5_03_TableauMaxAt` | Standard-tableau and entry-location vocabulary. |
| definition/interface | Def 5.4 | definition | Tableau coordinate space | `S05_Def5_04_TableauCoordinateSpace.lean` | `S05_Def5_04_tableauDim`, `S05_Def5_04_TableauSpace`, `S05_Def5_04_tableauBasisVec` | Tableau-count dimension and coordinate-space vocabulary. |
| definition/interface | Def 5.5 | definition | Contents and adjacent operators | `S05_Def5_05_ContentAndAdjacentOperators.lean` | `S05_Def5_05_cellContent`, `S05_Def5_05_entryContent`, `S05_Def5_05_youngAdjacentOperator`, `S05_Def5_05_diagonalContentOperator` | Contents, adjacent swap operators, and diagonal content operators. |
| proven | Lem 5.1 | lemma | Tableau Coxeter model for adjacent transpositions | `S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean` | `S05_Lem5_01_adjacentTranspositionsInYoungsBasis_coxeterModel` | Concrete tableau-coordinate Coxeter model. |
| proven | Lem 5.2 | lemma | Diagonal content eigenspaces | `S05_Lem5_02_DiagonalContentEigenspaces.lean` | `S05_Lem5_02_tableauContentSequence_injective`, `S05_Lem5_02_diagonalContentEigenspaces` | Explicit diagonal content operators; Appendix A supplies the group-algebra identification. |
| definition/interface | Def 5.6 | definition | Young block | `S05_Def5_06_YoungBlock.lean` | `S05_YoungBlock` | Young-block index vocabulary. |
| definition/interface | Def 5.7 | definition | Young-block energy profile | `S05_Def5_07_YoungBlockEnergyProfile.lean` | `S05_Def5_07_YoungBlockEnergyProfile` | Nonnegative numerical block-energy profile interface. |
| definition/interface | Def 5.8 | definition | U1-compatible Young-block profile | `S05_Def5_08_U1CompatibleYoungBlockProfile.lean` | `S05_Def5_08_U1CompatibleYoungBlockProfile` | Numerical interface identifying the one-row and standard blocks with `U_1`. |
| definition/interface | Def 5.9 | definition | Two-box removals | `S05_Def5_09_TwoBoxRemovals.lean` | `S05_IsHorizontalTwoBoxRemoval`, `S05_IsVerticalTwoBoxRemoval` | Horizontal and vertical two-box removal predicates. |
| definition/interface | Def 5.10 | definition | Signed two-box removals | `S05_Def5_10_SignedTwoBoxRemovals.lean` | `S05_PositiveSignedTwoBoxRemoval`, `S05_NegativeSignedTwoBoxRemoval` | Signed removal predicates. |
| definition/interface | Def 5.11 | definition | One-box removals | `S05_Def5_11_OneBoxRemovals.lean` | `S05_IsOneBoxRemoval`, `S05_oneBoxChildrenOdd` | One-box removal vocabulary. |
| proven | Lem 5.3 | lemma | Two-box tableau branching | `S05_Lem5_03_TwoBoxTableauBranching.lean` | `S05_Lem5_03_iterated_deletion_tableauContentSequence`, `S05_Lem5_03_twoStepDeletionTableauxEquivChildTableaux` | Fixed two-step tableau deletion equivalence. |
| definition/interface | Def 5.12 | definition | One-box deletion spaces | `S05_Def5_12_OneBoxDeletionSpaces.lean` | `S05_Def5_12_OneBoxDeletionTableaux`, `S05_Def5_12_existsUnique_tableauMaxAt` | Deletion-fiber coordinate space vocabulary. |
| proven | Lem 5.4 | lemma | One-box corner decomposition | `S05_Lem5_04_OneBoxCornerDecomposition.lean` | `S05_Lem5_04_row_form`, `S05_Lem5_04_removable_corner`, `S05_Lem5_04_tableau_unique_removable_corner` | Row form and removable-corner facts. |
| proven | Lem 5.5 | lemma | One-box deletion is unitary | `S05_Lem5_05_OneBoxDeletionIsUnitary.lean` | `S05_Lem5_05_oneBoxDeletionTableauxEquivChildTableauxOfOneBoxChildRow`, `S05_Lem5_05_deletionCoordinateMap_inner` | Coordinate inner-product preservation. |
| proven | Lem 5.6 | lemma | One-box deletion intertwines earlier swaps | `S05_Lem5_06_OneBoxDeletionIntertwinesEarlierSwaps.lean` | `S05_Lem5_06_deletionCoordinateMap_youngAdjacentOperator_intertwines`, `S05_Lem5_06_deletionCoordinateMap_diagonalContent_intertwines` | Coordinate-level intertwining for deletion fibers. |
| definition/interface | Def 5.13 | definition | Even sign-pattern multiset | `S05_Def5_13_EvenSignPatternMultiset.lean` | `S05_evenZeroSignPatternCount`, `S05_evenHighSignPatternCount` | Even sign-pattern counters. |
| definition/interface | Def 5.14 | definition | Odd sign-pattern multiset | `S05_Def5_14_OddSignPatternMultiset.lean` | `S05_oddHighSignPatternCount` | Odd sign-pattern counter. |
| proven | Lem 5.7 | lemma | Two-box dimension recursion | `S05_Lem5_07_TwoBoxDimensionRecursion.lean` | `S05_Lem5_07_tableauDim_twoStrip_branching_sized` | Tableau-count two-strip branching. |
| proven | Lem 5.8 | lemma | One-box dimension recursion | `S05_Lem5_08_OneBoxDimensionRecursion.lean` | `S05_Lem5_08_tableauDim_oneBoxChildrenOdd_branching` | Tableau-count one-box branching. |
| proven | Lem 5.9 | lemma | Sizes of the sign-pattern multisets | `S05_Lem5_09_SizesOfTheSignPatternMultisets.lean` | `S05_Lem5_09_tableauDim_twoStrip_size`, `S05_Lem5_09_tableauDim_oneBox_size` | Tableau-count size recurrences. |
| definition/interface | Def 5.15 | definition | Matching characters | `S05_Def5_15_MatchingCharacters.lean` | `S05_matchingCharacter`, `S05_matchingCharacter_cubeXor` | Matching-cube character vocabulary. |
| definition/interface | Def 5.16 | definition | Even matching eigenvector predicate | `S05_Def5_16_IsMatchingEigenvectorEven.lean` | `S05_IsMatchingEigenvectorEven` | Simultaneous even matching-edge eigenvector predicate. |
| definition/interface | Def 5.17 | definition | Odd matching eigenvector predicate | `S05_Def5_17_IsMatchingEigenvectorOdd.lean` | `S05_IsMatchingEigenvectorOdd` | Simultaneous odd matching-edge eigenvector predicate. |
| definition/interface | Def 5.18 | definition | Even matching-restriction scalar input | `S05_Def5_18_MatchingRestrictionEvenInput.lean` | `MatchingRestrictionEvenInput` | Even scalar input extracted from matching restriction. |
| definition/interface | Def 5.19 | definition | Odd matching-restriction scalar input | `S05_Def5_19_MatchingRestrictionOddInput.lean` | `MatchingRestrictionOddInput` | Odd scalar input extracted from matching restriction. |
| proven | Lem 5.10 | lemma | Matching subgroup eigenbasis | `S05_Lem5_10_MatchingSubgroupEigenbasis.lean` | `S05_Lem5_10_matchingSignProjectionEven_isMatchingEigenvector`, `S05_Lem5_10_matchingSignProjectionOdd_isMatchingEigenvector` | Concrete matching-operator and sign-projection wrappers are proved; Specht/Pieri restriction content is bundled into the spectral-block model boundary. |
| proven | Lem 5.11 | lemma | Local truncation on a matching character | `S05_Lem5_11_LocalTruncationOnAMatchingCharacter.lean` | `S05_Lem5_11_matchingLocalProjection_preserves_low_matchingCharacter`, `S05_Lem5_11_matchingLocalProjection_kills_high_matchingCharacter` | Matching-cube Fourier calculation. |
| definition/interface | Def 5.20 | definition | Even local-truncation trace input | `S05_Def5_20_TraceLocalTruncationEvenInput.lean` | `TraceLocalTruncationEvenInput` | Scalar trace formula interface for one even Young block. |
| definition/interface | Def 5.21 | definition | Odd local-truncation trace input | `S05_Def5_21_TraceLocalTruncationOddInput.lean` | `TraceLocalTruncationOddInput` | Scalar trace formula interface for one odd Young block. |
| external: block trace model input | Lem 5.12 | lemma | Trace of one local truncation on one Young block | `S05_Lem5_12_TraceOfOneLocalTruncationOnOneYoungBlock.lean` | `traceLocalTruncation_even_from_restriction`, `traceLocalTruncation_odd_from_restriction` | Trace formula wrappers from explicit scalar inputs. |
| proven | Def 5.22 | definition | Matching idempotents | `S05_Def5_22_MatchingIdempotents.lean` | `S05_matchingLowIdempotent`, `S05_matchingHighIdempotent`, `S05_matchingLow_add_matchingHigh` | Low/high idempotent vocabulary plus complementary idempotence proofs. |
| proven | Lem 5.13 | lemma | Local truncation as convolution | `S05_Lem5_13_LocalTruncationAsConvolution.lean` | `S05_Lem5_13_local_truncation_as_convolution` | Local projection as low convolution and residual as high convolution. |
| external: Young-block centrality input | Lem 5.14 | lemma | Central averaged rejection | `S05_Lem5_14_CentralAveragedRejection.lean` | `S05_Lem5_14_matchingMeanProjectionError_eq_average`, `S05_Lem5_14_matchingMeanProjectionError_eq_high_idempotent_average` | Finite-average and high-idempotent norm identities are proved; centrality on Young blocks is part of the spectral-block model boundary. |
| definition/interface | Def 5.23 | definition | Young-basis scalar commutant input | `S05_Def5_23_YoungBasisScalarCommutantInput.lean` | `S05_Def5_23_YoungBasisScalarCommutantInput` | Scalarity interface consumed by the spectral bridge. |
| external: scalar commutant input | Lem 5.15 | lemma | Young-basis scalar commutant | `S05_Lem5_15_YoungBasisScalarCommutant.lean` | `S05_Lem5_15_matchingAverageScalarity_eq_sum` | Projection from the explicit scalarity input to the weighted-sum identity. |
| external: trace/scalar model input | Lem 5.16 | lemma | Block scalar of the averaged rejection | `S05_Lem5_16_BlockScalarOfTheAveragedRejection.lean` | `S05_Lem5_16_scalar_eq_trace_div_dimension`, `S05_Lem5_16_even_scalar_eq_hEven_div_dim` | Trace-divided-by-dimension algebra from explicit scalarity and trace identities. |
| proven | Lem 5.17 | lemma | Block lower bound implies the gap | `S05_Lem5_17_BlockLowerBoundImpliesTheGap.lean` | `S05_Lem5_17_spectralGapFromBlockScalars`, `S05_Lem5_17_spectralGapFromBlockModelWithDim` | Weighted-sum spectral-gap algebra. |
| proven | Lem 5.18 | lemma | Regular Young-block decomposition | `S05_Lem5_18_RegularYoungBlockDecomposition.lean` | `spectralBlockModelInputWithDim_even_from_appendixA`, `spectralBlockModelInputWithDim_odd_from_appendixA` | Assembly from Appendix A inputs into the `SpectralBlockModelInputWithDim` interface. |
| proven | Lem 5.19 | lemma | Even spectral bridge | `S05_Lem5_19_EvenSpectralBridge.lean` | `S05_Lem5_19_tableauDim_evenSpectralGapFromCertificates` | Algebraic bridge from explicit `SpectralBlockModelInputWithDim` hypothesis and finite certificate. |
| proven | Lem 5.20 | lemma | Odd spectral bridge | `S05_Lem5_20_OddSpectralBridge.lean` | `S05_Lem5_20_tableauDim_oddSpectralGapFromCertificates` | Algebraic bridge from explicit `SpectralBlockModelInputWithDim` hypothesis and finite certificate. |
| proven | Lem 5.21 | lemma | Counting one more matching edge | `S05_Lem5_21_CountingOneMoreMatchingEdge.lean` | `S05_Lem5_21_counting_one_more_matching_edge` | Finite counting lemma. |
| proven | Lem 5.22 | lemma | Weight-zero entries are never a majority | `S05_Lem5_22_WeightZeroEntriesAreNeverAMajority.lean` | `S05_Lem5_22_tableau_weightZeroEntries_never_majority` | Tableau-count z-bound certificate. |
| proven | Lem 5.23 | lemma | Where the induction can fail | `S05_Lem5_23_WhereTheInductionCanFail.lean` | `S05_Lem5_23_where_the_induction_can_fail` | Exceptional-shape localization. |
| proven | Lem 5.24 | lemma | Even certificate | `S05_Lem5_24_EvenCertificate.lean` | `S05_Lem5_24_tableau_even_certificate` | Tableau-count even certificate; reusable height definition is in `Aux_Def_TableauEvenHeight.lean`. |
| proven | Lem 5.25 | lemma | Odd exceptional children | `S05_Lem5_25_OddExceptionalChildren.lean` | `S05_Lem5_25_odd_exceptional_children` | Odd exceptional child analysis. |
| proven | Lem 5.26 | lemma | Odd certificate | `S05_Lem5_26_OddCertificate.lean` | `S05_Lem5_26_tableau_odd_certificate` | Tableau-count odd certificate; reusable height definition is in `Aux_Def_TableauOddHeight.lean`. |

Notes:

- `proven` means the Lean file proves the stated coordinate/combinatorial wrapper without new external assumptions.
- `definition/interface` means the file introduces vocabulary used later.
- `external: ...` rows name the representation-theoretic input being used.
- Neutral height definitions used by both Appendix A.2 and the finite certificate proofs are split into `Aux_Def_TableauEvenHeight.lean` and `Aux_Def_TableauOddHeight.lean`; they are not separate numbered paper theorem statements.
