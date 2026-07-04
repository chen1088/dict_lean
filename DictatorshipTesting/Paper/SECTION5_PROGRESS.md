# Section 5 Progress

## TableauDim Certificate Migration Batch

Completed commits from the current milestone:
- `70ccd94` Port z-bound certificate to tableauDim
- `39e7c3f` Add tableauDim generic even certificate step
- `2c3fa74` Add tableauDim reusable even certificate facts
- `db54770` Add exact tableauDim formulas for even certificates
- `0f16319` Add tableauDim two-row even exception certificate
- `9e1c2e0` Port three-row even tableau exception
- `4648019` Port two-row three even tableau exception
- `24ee3d4` Finish tableauDim even certificate
- `a111e25` Port odd certificate to tableauDim

Main names added in this batch:
- `zEven_le_half_tableauDim_of_not_oneRow_finite_induction`
- `S05_Lem5_32_tableau_weightZeroEntries_never_majority`
- `zEven_le_tableauDim`
- `tableauDim_standardDiagramEven_formula`
- `tableauDim_twoRowTwoDiagramEven_formula`
- `hEvenTableau`
- `hEvenTableau_ge_one_fifth_tableauDim_generic_step_succ`
- `hEvenTableau_oneRowDiagram`
- `hEvenTableau_standardDiagramEven_formula`
- `hEvenTableau_nonneg`
- `hEvenTableau_twoRowTwoDiagramEven_formula`
- `hEvenTableau_ge_one_fifth_tableauDim_twoRowTwoException`
- `hEvenTableau_twoRowOneOneDiagramEven_formula`
- `tableauDim_twoRowOneOneDiagramEven_formula`
- `hEvenTableau_ge_one_fifth_tableauDim_twoRowOneOneException`
- `hEvenTableau_ge_one_fifth_tableauDim_twoRowThreeException`
- `hEvenTableau_ge_one_fifth_tableauDim_threeRowTwoOneException`
- `S05_Lem5_34_tableau_even_certificate`
- `hOddTableau`
- `hOddTableau_ge_one_sixth_tableauDim_odd_exceptional`
- `S05_Lem5_36_tableau_odd_certificate`

Status:
- Lemma 5.32 now has an axiom-free tableau-count version.  The old
  `youngDim` theorem remains for the current spectral bridge, but the finite
  `zEven` proof no longer needs the two-strip `youngDim` branching input when
  stated against `tableauDim`.
- Lemma 5.34 has a parallel tableau-count height recurrence `hEvenTableau`.
  The generic induction step, one-row and standard height facts, all four
  exceptional families, and the final certificate
  `S05_Lem5_34_tableau_even_certificate` are proved against `tableauDim`.
- Lemma 5.36 now has a parallel tableau-count height recurrence `hOddTableau`.
  The two odd exceptional families, the generic one-box reduction, and the final
  certificate `S05_Lem5_36_tableau_odd_certificate` are proved against
  `tableauDim`.
- The active Theorem 4.10 path still depends on the old `youngDim` spectral
  model.  The files `S05_Lem5_28_BlockLowerBoundImpliesTheGap.lean`,
  `S05_Lem5_29_EvenSpectralBridge.lean`, `S05_Lem5_30_OddSpectralBridge.lean`,
  and `Aux_SpectralBridgeRepresentationInputs.lean` all state their block
  lower bounds and trace identities using `youngDim`.  A tableauDim finite
  certificate therefore cannot be consumed by Theorem 4.10 until either:
  `tableauDim = youngDim` is proved for the relevant diagrams, or the spectral
  block model is parameterized so its dimension slot can be instantiated by
  `tableauDim`.

## This Run

### Two-box tableau-count batch

Completed commits:
- `9d8d578` Define two-step removable-row deletion
- `c285ce9` Add coordinates for two-step deletions
- `f57a3a1` Relate two-step deletions to strip directions
- `1a15282` Count tableaux in a fixed two-step deletion fiber
- `1cfcf0e` Define canonical two-step data of a tableau
- `9b26e41` Sum tableau dimension over ordered two-step deletions
- `cee03dc` Expose sized two-strip child interface for tableau counts
- `b27bc09` Expose ordered tableau-count recursion in Lemma 5.15
- `919d1e1` Define tagged two-strip children
- `53695cc` Map ordered deletions to tagged two-strip children
- `486b26b` Add positive row API for two-strip reindexing
- `f835646` Construct ordered deletions from tagged two-strip children
- `39e4c7a` Prove tagged child reconstruction preserves tags
- `7b84a07` Prove tableau-count two-strip branching

Main names added:
- `TwoStepRemovableRows`
- `twoStepRemovableRowsEquivSigma`
- `deleteTwoRemovableRowsDiagram`
- `deleteTwoRemovableRows_isYoungSubdiagram`
- `sum_row_diff_deleteTwoRemovableRows`
- `firstDeletedCornerOfTwoStep`
- `secondDeletedCornerOfTwoStepInChild`
- `secondDeletedCornerOfTwoStepInParent`
- `deleteTwoRemovableRows_vertical_of_distinct_rows`
- `deleteTwoRemovableRows_horizontal_of_same_row`
- `deleteTwoRemovableRows_horizontal_or_vertical`
- `TwoStepDeletionTableaux`
- `twoStepDeletionTableauxEquivChildTableaux`
- `card_twoStepDeletionTableaux_eq_child`
- `tableauDim_fixed_twoStepDeletion`
- `tableauDim_eq_sum_twoStepRemovableRows`
- `deleteMaxAtMaxRemovableRow`
- `twoStepDataOfTableau`
- `tableau_mem_twoStepDataOfTableau`
- `horizontalTwoStripChildrenSized`
- `verticalTwoStripChildrenSized`
- `TaggedTwoStripChildrenSized`
- `taggedTwoStripChildDiagram`
- `sum_taggedTwoStripChildrenSized`
- `deleteTwoRemovableRows_mem_horizontal_or_vertical_sized`
- `deleteTwoRemovableRows_horizontal_of_first_le_second`
- `deleteTwoRemovableRows_vertical_of_second_lt_first`
- `twoStepToTaggedTwoStripChild`
- `taggedTwoStripChildDiagram_twoStepToTagged`
- `taggedTwoStripChildToTwoStep`
- `twoStepToTagged_taggedTwoStripChildToTwoStep`
- `taggedTwoStripChildToTwoStep_twoStepToTagged`
- `twoStepRemovableRowsEquivTaggedTwoStripChildren`
- `sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren`
- `tableauDim_twoStrip_branching_sized`
- `S05_Lem5_15_tableauDim_fixed_twoStepDeletion`
- `S05_Lem5_15_tableauDim_ordered_twoStep_branching`
- `S05_Lem5_15_twoStepDeletion_horizontal_or_vertical`
- `S05_Lem5_15_twoStepRemovableRowsEquivTaggedTwoStripChildren`
- `S05_Lem5_15_sum_twoStepRemovableRows_eq_sum_taggedTwoStripChildren`
- `S05_Lem5_15_tableauDim_twoStrip_branching_sized`

Status:
- `tableauDim` ordered two-step recursion is proved.
- The multiplicity-preserving reindexing between ordered two-step removable-row
  deletions and the disjoint tagged sum of horizontal and vertical two-strip
  children is proved.  Disconnected two-box skew shapes are handled by the tag:
  the two deletion orders map to the horizontal and vertical copies separately.
- The sized horizontal-plus-vertical two-strip recursion for `tableauDim` is
  proved as `tableauDim_twoStrip_branching_sized` and exposed in Lemma 5.15 as
  `S05_Lem5_15_tableauDim_twoStrip_branching_sized`.
- The old `youngDim` two-strip recursion remains external because `youngDim` is
  still the hook-length proxy.  Removing that assumption still requires either
  the hook-length/tableau-count equality or migrating downstream certificates to
  `tableauDim`.

Completed commits:
- `6ba8505` Add adjacent value swap for Lemma 5.1
- `d796ef7` Add swapped-tableau case for Lemma 5.1
- `0d0d35c` Add content API for Lemma 5.2
- `0721c63` Track cells under adjacent tableau swap
- `bc88b48` Add content-sequence API for Lemma 5.2
- `7e7b8a8` Clarify Young block interface files
- `132a1b3` Add row combinatorics for strip removals
- `ba0eb24` Start basis-level two-box tableau branching
- `e8adde1` Expose sign-pattern size interfaces
- `d167717` Expand matching character and idempotent interfaces
- `b450942` Expose averaged rejection definitions
- `c648518` Clarify spectral bridge paper-facing wrappers
- `43450b8` Add paper-numbered finite certificate aliases
- `f6729d5` Extend deletion content-sequence compatibility
- `c702f90` Expose one-box deletion corner interfaces
- `c12c502` Expose one-box deletion cell equivalence facts
- `29ce495` Expose two-box first deletion content compatibility
- `6e76a08` Expose two-box first deletion cell compatibility
- `bc5b547` Add iterated two-box deletion interface
- `e9e0510` Extend iterated deletion cell compatibility
- `b8355d8` Expose signed two-box row conditions
- `d4ddd46` Expose one-box removal row and corner facts
- `ad739ed` Expose sign-pattern size base cases
- `d8aa8c5` Expose matching character algebra facts
- `804cd62` Expose matching-character truncation dichotomy
- `78aec24` Add tableau-count dimension
- `8754b57` Add removable-row tableau dimension helpers
- `7079695` Control last row after removable deletion
- `7b389bf` Construct child diagram by deleting a removable row
- `8a28cc8` Relate removable rows and one-box children
- `b5fca2e` Relate max removable row to deleted corner
- `da83c7c` Count tableaux by maximum removable row fiber
- `1f8cd71` Sum tableau dimension over removable rows
- `07bfda0` Prove one-box tableau-count branching
- `475dab0` Expose tableau-count one-box recursion in Lemma 5.16

Files changed:
- `DictatorshipTesting/Paper/Aux_YoungAdjacentEntries.lean`
- `DictatorshipTesting/Paper/Aux_YoungDiagramCorners.lean`
- `DictatorshipTesting/Paper/S05_Lem5_01_AdjacentTranspositionsInYoungsBasis.lean`
- `DictatorshipTesting/Paper/S05_Lem5_02_JucysMurphyEigenbasis.lean`
- `DictatorshipTesting/Paper/S05_Def5_03_YoungBlock.lean`
- `DictatorshipTesting/Paper/S05_Lem5_04_RegularYoungBlocks.lean`
- `DictatorshipTesting/Paper/S05_Def5_05_TwoBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Def5_06_SignedTwoBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Def5_07_OneBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Lem5_17_SizesOfTheSignPatternMultisets.lean`
- `DictatorshipTesting/Paper/S05_Def5_18_MatchingCharacters.lean`
- `DictatorshipTesting/Paper/S05_Lem5_20_LocalTruncationOnAMatchingCharacter.lean`
- `DictatorshipTesting/Paper/Aux_TableauDimension.lean`
- `DictatorshipTesting/PaperAux.lean`
- `DictatorshipTesting/Paper/S05_Lem5_16_OneBoxDimensionRecursion.lean`
- `DictatorshipTesting/Paper/S05_Lem5_08_TwoBoxTableauBranching.lean`
- `DictatorshipTesting/Paper/S05_Def5_13_EvenSignPatternMultiset.lean`
- `DictatorshipTesting/Paper/S05_Def5_14_OddSignPatternMultiset.lean`
- `DictatorshipTesting/Paper/S05_Lem5_17_SizesOfTheSignPatternMultisets.lean`
- `DictatorshipTesting/Paper/S05_Def5_18_MatchingCharacters.lean`
- `DictatorshipTesting/Paper/S05_Lem5_20_LocalTruncationOnAMatchingCharacter.lean`
- `DictatorshipTesting/Paper/S05_Def5_22_MatchingIdempotents.lean`
- `DictatorshipTesting/Paper/S05_Lem5_23_LocalTruncationAsConvolution.lean`
- `DictatorshipTesting/Paper/S05_Lem5_24_CentralAveragedRejection.lean`
- `DictatorshipTesting/Paper/S05_Lem5_25_YoungBasisScalarCommutant.lean`
- `DictatorshipTesting/Paper/S05_Lem5_26_BlockScalarOfTheAveragedRejection.lean`
- `DictatorshipTesting/Paper/S05_Lem5_27_TheDegreeOneSpaceAsYoungBlocks.lean`
- `DictatorshipTesting/Paper/S05_Lem5_28_BlockLowerBoundImpliesTheGap.lean`
- `DictatorshipTesting/Paper/S05_Lem5_29_EvenSpectralBridge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_30_OddSpectralBridge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_31_CountingOneMoreMatchingEdge.lean`
- `DictatorshipTesting/Paper/S05_Lem5_32_WeightZeroEntriesAreNeverAMajority.lean`
- `DictatorshipTesting/Paper/S05_Lem5_34_EvenCertificate.lean`
- `DictatorshipTesting/Paper/S05_Lem5_36_OddCertificate.lean`
- `DictatorshipTesting/Paper/S05_Def5_09_OneBoxDeletionSpaces.lean`
- `DictatorshipTesting/Paper/S05_Lem5_11_OneBoxDeletionIsUnitary.lean`
- `DictatorshipTesting/Paper/S05_Lem5_12_OneBoxDeletionIntertwinesEarlierSwaps.lean`
- `DictatorshipTesting/Paper/S05_Def5_06_SignedTwoBoxRemovals.lean`
- `DictatorshipTesting/Paper/S05_Def5_07_OneBoxRemovals.lean`

Main names added:
- `adjacentSwapValue`, `adjacentSwapEntry`
- `adjacentSwapEntry_loCell`, `adjacentSwapEntry_hiCell`
- `adjacentSwapEntry_of_ne_lo_hi`, `adjacentSwapEntry_involutive`
- `adjacentSwapEntry_bijective`
- `adjacentSwapValue_lt_of_lt_of_not_adjacent_pair`
- `adjacentSwapTableau`
- `adjacentSwapTableau_cell_lo`, `adjacentSwapTableau_cell_hi`
- `adjacentSwapTableau_cell_of_ne_lo_hi`
- `adjacentSwapTableau_entryContent_lo`
- `adjacentSwapTableau_entryContent_hi`
- `adjacentSwapTableau_entryContent_of_ne_lo_hi`
- `S05_Lem5_01_adjacentSwapEntry_loCell`
- `S05_Lem5_01_adjacentSwapEntry_hiCell`
- `S05_Lem5_01_adjacentSwapEntry_bijective`
- `S05_Lem5_01_adjacentSwapTableau`
- `S05_Lem5_01_adjacentSwapTableau_cell_lo`
- `S05_Lem5_01_adjacentSwapTableau_cell_hi`
- `S05_Lem5_01_adjacentSwapTableau_cell_of_ne_lo_hi`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_lo`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_hi`
- `S05_Lem5_01_adjacentSwapTableau_entryContent_of_ne_lo_hi`
- `tableauContentSequence`
- `tableauContentSequence_adjacentSwap_lo`
- `tableauContentSequence_adjacentSwap_hi`
- `tableauContentSequence_adjacentSwap_of_ne_lo_hi`
- `S05_Lem5_02_cellContent`, `S05_Lem5_02_entryContent`
- `S05_Lem5_02_tableauContentSequence`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_lo`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_hi`
- `S05_Lem5_02_tableauContentSequence_adjacentSwap_of_ne_lo_hi`
- `S05_Lem5_02_entryContent_adjacent_hi_eq_lo_add_one_of_sameRow`
- `S05_Lem5_02_entryContent_adjacent_hi_eq_lo_sub_one_of_sameCol`
- `S05_Lem5_02_entryContent_adjacent_lo_eq_hi_sub_one_of_sameRow`
- `S05_Lem5_02_entryContent_adjacent_lo_eq_hi_add_one_of_sameCol`
- `S05_Def5_03_YoungBlockEnergyModel`
- `S05_Def5_03_MatchingAverageScalarModel`
- `S05_Def5_03_SpectralBlockModelInput`
- `S05_Lem5_04_YoungBlockDecompositionInput`
- `S05_Lem5_04_U1YoungBlockIdentificationInput`
- `S05_Lem5_04_blockEnergy_nonnegative`
- `S05_Lem5_04_u1_identification`
- `youngRow_sum_range_add_two`
- `sum_row_diff_of_twoBoxSubdiagram`
- `sum_row_diff_of_horizontalTwoStripChild`
- `sum_row_diff_of_verticalTwoStripChild`
- `row_le_parent_of_twoBoxSubdiagram`
- `row_le_parent_of_horizontalTwoStripChild`
- `row_le_parent_of_verticalTwoStripChild`
- `next_parent_row_le_child_row_of_horizontalTwoStripChild`
- `parent_row_le_child_row_add_one_of_verticalTwoStripChild`
- `row_diff_le_one_of_verticalTwoStripChild`
- `S05_Def5_05_sum_row_diff_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_sum_row_diff_of_verticalTwoBoxRemoval`
- `S05_Def5_05_row_le_parent_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_row_le_parent_of_verticalTwoBoxRemoval`
- `S05_Def5_05_next_parent_row_le_child_row_of_horizontalTwoBoxRemoval`
- `S05_Def5_05_parent_row_le_child_row_add_one_of_verticalTwoBoxRemoval`
- `S05_Def5_05_row_diff_le_one_of_verticalTwoBoxRemoval`
- `S05_PositiveSignedTwoBoxRemoval`
- `S05_NegativeSignedTwoBoxRemoval`
- `S05_Def5_06_sum_row_diff_of_positiveSignedTwoBoxRemoval`
- `S05_Def5_06_sum_row_diff_of_negativeSignedTwoBoxRemoval`
- `S05_Def5_07_existsUnique_row_of_oneBoxRemoval`
- `S05_Def5_07_exists_removableRow_of_oneBoxRemoval`
- `S05_Lem5_08_deleteFirstMaxAsTableau`
- `S05_Lem5_08_first_deleted_cell_removable_corner`
- `S05_Lem5_08_after_first_deletion_unique_second_corner`
- `S05_Lem5_08_second_deleted_cell_removable_corner`
- `S05_evenZeroSignPatternCount_zero`
- `S05_evenZeroSignPatternCount_succ`
- `S05_evenHighSignPatternCount_zero`
- `S05_evenHighSignPatternCount_succ`
- `S05_oddHighSignPatternCount_eq_evenHigh_sum`
- `S05_Lem5_17_evenZeroSignPatternCount_succ`
- `S05_Lem5_17_evenHighSignPatternCount_succ`
- `S05_Lem5_17_oddHighSignPatternCount_eq_evenHigh_sum`
- `S05_Lem5_17_youngDim_twoStrip_size`
- `S05_Lem5_17_youngDim_oneBox_size`
- `S05_matchingCharacterWeight`
- `S05_matchingCharacterLow`, `S05_matchingCharacterHigh`
- `S05_matchingCharacter_empty`
- `S05_matchingCharacterWeight_empty`
- `S05_matchingCharacterLow_empty`
- `S05_matchingCharacterWeight_singleton`
- `S05_matchingCharacterLow_singleton`
- `S05_not_low_and_high`
- `S05_matchingCharacter_low_or_high`
- `S05_Lem5_20_cubeLowDegreeOnePart_matchingCharacter_of_low`
- `S05_Lem5_20_cubeLowDegreeOnePart_matchingCharacter_of_high`
- `S05_Lem5_20_matchingLocalProjection_preserves_low_matchingCharacter`
- `S05_Lem5_20_matchingLocalProjection_kills_high_matchingCharacter`
- `S05_matchingLowCharacterSet`, `S05_matchingHighCharacterSet`
- `S05_mem_matchingLowCharacterSet_iff`
- `S05_mem_matchingHighCharacterSet_iff`
- `S05_matchingLowIdempotent_apply`
- `S05_matchingHighIdempotent_apply`
- `S05_Lem5_23_local_truncation_eq_low_idempotent`
- `S05_Lem5_23_residual_eq_high_idempotent`
- `S05_Lem5_24_matchingLocalProjectionError_eq_l2DistSq`
- `S05_Lem5_24_matchingMeanProjectionError_eq_average`
- `S05_Lem5_25_YoungBasisScalarCommutantInput`
- `S05_Lem5_25_matchingAverageScalarity_eq_sum`
- `S05_Lem5_26_scalar_eq_trace_div_dimension`
- `S05_Lem5_26_even_scalar_eq_hEven_div_dim`
- `S05_Lem5_26_odd_scalar_eq_hOdd_div_dim`
- `S05_nonU1YoungBlocks`
- `S05_mem_nonU1YoungBlocks_iff`
- `S05_Lem5_27_l2DistSqToU1_eq_nonU1_sum`
- `S05_Lem5_28_spectralGapFromBlockScalars`
- `S05_Lem5_28_blockScalar_lower_bound_of_traceScalarFormula`
- `S05_Lem5_28_traceScalarValue_of_blockTraceIdentity`
- `S05_Lem5_29_evenSpectralGapFromCertificates`
- `S05_Lem5_30_oddSpectralGapFromCertificates`
- `S05_Lem5_31_counting_one_more_matching_edge`
- `S05_Lem5_32_weightZeroEntries_never_majority`
- `S05_Lem5_32_zEven_le_youngDim`
- `S05_Lem5_34_even_certificate`
- `S05_Lem5_36_odd_certificate`
- `S05_Def5_09_existsUnique_tableauMaxAt`
- `S05_Lem5_11_deletedCornerCell_row`
- `S05_Lem5_11_deletedCornerCell_col`
- `S05_Lem5_11_insertMax_entry_deletedCorner`
- `S05_Lem5_11_insertMax_entry_ne_deletedCorner`
- `S05_Lem5_11_youngCellExceptEquivChild_to_row`
- `S05_Lem5_11_youngCellExceptEquivChild_to_col`
- `S05_Lem5_11_youngCellExceptEquivChild_symm_row`
- `S05_Lem5_11_youngCellExceptEquivChild_symm_col`
- `S05_Lem5_11_insertMax_entry_lt_last_of_ne_deletedCorner`
- `S05_Lem5_12_deleteMax_tableauContentSequence`
- `S05_Lem5_08_first_deletion_tableauContentSequence`
- `S05_Lem5_08_first_deletion_childCellToParent_cellOfEntry`
- `S05_Lem5_08_first_deletion_cellOfEntry_row`
- `S05_Lem5_08_first_deletion_cellOfEntry_col`
- `S05_Lem5_08_deleteSecondMaxAsTableau`
- `S05_Lem5_08_second_deletion_tableauContentSequence`
- `S05_Lem5_08_iterated_deletion_tableauContentSequence`
- `S05_Lem5_08_second_deletion_childCellToParent_cellOfEntry`
- `S05_Lem5_08_second_deletion_cellOfEntry_row`
- `S05_Lem5_08_second_deletion_cellOfEntry_col`
- `S05_Lem5_08_iterated_deletion_cellOfEntry_row`
- `S05_Lem5_08_iterated_deletion_cellOfEntry_col`
- `S05_Def5_06_row_le_parent_of_positiveSignedTwoBoxRemoval`
- `S05_Def5_06_row_le_parent_of_negativeSignedTwoBoxRemoval`
- `S05_Def5_06_next_parent_row_le_child_row_of_positiveSignedTwoBoxRemoval`
- `S05_Def5_06_parent_row_le_child_row_add_one_of_negativeSignedTwoBoxRemoval`
- `S05_Def5_06_row_diff_le_one_of_negativeSignedTwoBoxRemoval`
- `S05_Def5_07_sum_row_diff_of_oneBoxRemoval`
- `S05_Def5_07_exists_removableCornerBox_of_oneBoxRemoval`
- `S05_Lem5_17_evenZeroSignPatternCount_zero`
- `S05_Lem5_17_evenHighSignPatternCount_zero`
- `S05_matchingCharacter_ne_zero`
- `S05_matchingCharacter_mul_self`
- `S05_matchingCharacter_cubeXor`
- `S05_Lem5_20_cubeLowDegreeOnePart_matchingCharacter_preserved_or_killed`
- `standardYoungTableauFintype`
- `tableauMaxAtSubtypeFintype`
- `tableauDimNat`
- `tableauDim`
- `tableauDim_nonneg`
- `card_tableaux_maxAt_deletedCorner_eq_child`
- `tableauDim_fixed_oneBoxChild`
- `removableRow_lt_size`
- `youngRow_last_eq_zero_of_removable_lt`
- `youngRow_last_eq_one_of_removable_not_lt`
- `deleteRemovableRowDiagram`
- `youngRow_deleteRemovableRowDiagram`
- `deleteRemovableRowDiagram_isOneBoxChild`
- `row_form_deleteRemovableRowDiagram`
- `RemovableRow`
- `removableRowToOneBoxChild`
- `removableRowToOneBoxChild_mem`
- `oneBoxChildToRemovableRow`
- `oneBoxChildToRemovableRow_row_form`
- `deletedCornerCell_removableCornerBox_of_removableRow`
- `maxRemovableRow_eq_of_tableauMaxAt_deletedCorner`
- `maxRemovableRowFiberEquivDeletedCorner`
- `card_maxRemovableRow_fiber_eq_deletedCorner`
- `card_maxRemovableRow_fiber_eq_child`
- `standardYoungTableauEquivSigmaMaxRemovableRow`
- `card_standardYoungTableau_eq_sum_maxRemovableRow_fibers`
- `card_standardYoungTableau_eq_sum_removableRow_children`
- `tableauDim_eq_sum_removableRow_children`
- `youngDiagram_ext_youngRow`
- `oneBoxChildrenSized`
- `removableRowToOneBoxChild_mem_sized`
- `oneBoxChildToRemovableRowSized`
- `oneBoxChildToRemovableRowSized_row_form`
- `oneBoxChildToRemovableRowSized_removableRowToOneBoxChild`
- `removableRowToOneBoxChild_oneBoxChildToRemovableRowSized`
- `removableRowsEquivOneBoxChildren`
- `sum_removableRows_tableauDim_eq_oneBoxChildrenSized`
- `tableauDim_oneBox_branching_sized`
- `oneBoxChildrenSized_eq_oneBoxChildrenOdd`
- `tableauDim_oneBoxChildrenOdd_branching`
- `S05_Lem5_16_tableauDim_fixed_oneBoxChild`
- `S05_Lem5_16_tableauDim_oneBox_branching`
- `S05_Lem5_16_tableauDim_oneBoxChildrenOdd_branching`

## Next Blocker

The one-box branching recursion is now proved for the assumption-free
tableau-count dimension `tableauDim`, including the odd-specialized form used by
Lemma 5.16.  The remaining blocker for removing the old `youngDim` ordinary
branching input is not one-box tableau counting; it is the separate theorem
identifying the hook-length proxy `youngDim` with the tableau-count dimension
`tableauDim`.

The remaining spectral bridge claims about Young's orthogonal matrices, the
operator-level Jucys--Murphy eigenbasis, Specht restriction, Young-block
scalarity, and Schur-lemma centrality are still representation-layer statements.
No new representation-theory input was introduced in this batch.

## Next Recommended Milestone

Use the completed one-box tableau-count layer as the template for the analogous
two-box tableau-count branching layer around Lemma 5.15.  Replacing the
hook-length `youngDim` axioms still requires a later theorem identifying
`tableauDim` with `youngDim`.
