# Section 5 Progress

Source checked: `../dictatorship_testing_soda27_latest.tex`.

## Spine Status

- Section 5 now has 30 numbered definitions and 27 numbered result statements
  (`lemma`, `proposition`, `theorem`, and `corollary` environments).  The two
  counters are separate.
- Section 5 paper-facing Lean file count is 57.
- Appendix A has 3 numbered external-input statements and 3 Lean-facing files.
- No two Section 5 definition files share a definition number, and no two
  Section 5 result files share a lemma/theorem number.
- Interface definitions formerly bundled into larger results are now exposed as
  Definitions 5.16--5.21 and 5.23.
- The regular Young-block decomposition assembly lemma is in Section 5:
  `S05_Lem5_19_RegularYoungBlockDecomposition.lean`.
- The degree-one Young-block input is in Appendix A:
  `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean`.

Detailed maps:

- `SECTION5_FILE_MAP.md`
- `APPENDIX_A_FILE_MAP.md`
- `DEFINITION_FILE_MAP.md`

## Latest Checkpoint

- Definition 5.6 is now only the Young-block index interface.
- Definitions 5.7 and 5.8 expose the Young-block energy profile and the
  `U_1`-compatible block profile.
- Definitions 5.16 and 5.17 expose the even and odd matching eigenvector
  predicates.
- Definitions 5.18 and 5.19 expose the even and odd matching-restriction scalar
  inputs.
- Definitions 5.20 and 5.21 expose the even and odd local-truncation trace
  inputs.
- Definition 5.23 exposes the Young-basis scalar commutant input.
- Lemma 5.3 proves connectedness of standard tableaux by transporting explicit
  adjacent-incomparable-swap paths between linear extensions.
- Lemma 5.7 coordinate-level deletion-fiber intertwining is proved:
  `S05_Lem5_07_deletionCoordinateMap_youngAdjacentOperator_intertwines`.
- Definitions 5.13 and 5.14 now contain genuine recursive
  `Multiset (Finset (Fin m))` label data rather than only scalar shadows.
- Lemma 5.10 proves the even/odd multiset cardinalities and identifies their
  empty/high multiplicities with `zEven`, `hEvenTableau`, and `hOddTableau`.
- Lemma 5.11 has proved matching eigenvalue preservation under one-edge
  projections, support-selected one-edge projections, and simultaneous matching
  sign projections.
- Lemma 5.11 now also proves the complete signed two-box child orthogonal
  decomposition: explicit coordinate embeddings, isometry, the final-edge
  sign, earlier-adjacent intertwining, pairwise-orthogonal ranges, and joint
  spanning of the parent tableau space.
- Lemma 5.11 now recursively constructs the canonical even matching basis from
  that decomposition. The family is an actual Mathlib basis, is orthonormal,
  spans, has the prescribed simultaneous canonical-edge eigenvalues, and its
  label enumeration is literally `S05_evenSignPatternMultiset` with
  multiplicity.
- Lemma 5.11 now transports that basis to every even matching. Endpoint
  coverage and the conjugating permutation are explicit; represented
  permutations are proved invertible and inner-product preserving; the
  transported basis has direct `M.toOrdered` character action and exact
  transported label multiplicity.
- Lemma 5.11 now also constructs the canonical odd basis from the one-box
  removable-row fibers. The family is an actual Mathlib basis, is orthonormal
  and spanning, inherits every matching eigenvalue through Lemma 5.7, and has
  literal label multiset `S05_oddSignPatternMultiset`.
- Lemma 5.11 proves the unique unmatched point for every odd matching, the
  endpoint-plus-unmatched conjugating permutation, and arbitrary odd transport
  with direct `M.toOrdered` character action and exact labels.
- Lemma 5.13 now instantiates the positive-size even and all odd tableau and
  full Young-block fixed-matching traces without an eigenbasis hypothesis.
- Definition 5.22 has proved low/high matching idempotent identities, zero
  cross-compositions, and the low-plus-high decomposition identity.
- Lemma 5.15 proves the finite-average/high-idempotent part of central averaged
  rejection.
- Lemma 5.16 now proves a generic Young-model scalar commutant theorem:
  a linear operator on one tableau-coordinate block that commutes with all
  diagonal content operators and all adjacent Young operators is scalar on the
  tableau basis, using the internally proved Lemma 5.3 connectedness theorem.
- Lemma 5.17a introduces `AveragedRejectionYoungOperatorData`, the one-block
  operator interface still needed for the averaged rejection operator.  It
  extracts adjacent/content commutation and applies Lemma 5.16.
- Definition 5.28 introduces a finite group-algebra action interface:
  `GroupAlgebraElement`, `rightConvolution`, `repOfGroupAlgebraElement`, and
  `YoungRepresentationActionData`.  It proves the adapter from such a
  representation-action package to `AveragedRejectionYoungOperatorData`.  It
  now also proves, by finite conjugation reindexing, that coefficient centrality
  implies commutation with represented group elements and arbitrary represented
  group-algebra sums.
- Definition 5.29 constructs the actual averaged high matching element `q`,
  proves its fixed-matching covariance and averaged coefficient centrality,
  identifies its right-convolution action with the average of the existing
  high matching idempotents, and constructs `rho_lambda(q)` with adjacent and
  content commutation for every supplied `YoungRepresentationActionData`.
  This gives `AveragedRejectionYoungOperatorData` and one-block scalarity.  The
  actual matching-character idempotents are now also represented explicitly;
  character orthogonality proves their eigenvector action and the `0/1` action
  of the fixed high element.
- Faithful operator-only Appendix A interfaces are now defined as
  `YoungOrthogonalActionData` and `JucysMurphyContentActionData`.  Their adapter
  constructs `YoungRepresentationActionData`, so A.1 action data plus A.2
  content data now reaches the concrete Definition 5.29 operator without
  putting scalarity into either external interface.  A.1 now identifies the
  literal adjacent swap `(a,a+1)`, rather than an arbitrary permutation, with
  the concrete Young adjacent operator.
- Definition 5.30 defines `tableauOperatorTrace`, proves the scalar trace and
  trace-division formulas, and proves that the concrete average trace is the
  average of the concrete fixed-matching traces.  It reduces each fixed trace
  to the sum of its high-character idempotent traces and proves the
  `tableauDim` left-index factor for the full matrix-coordinate block.
- Definition 5.30 now also identifies the coordinate trace with Mathlib's
  basis-independent linear-map trace.  Lemma 5.13 uses this to prove the actual
  even and odd fixed-matching tableau traces, and their full Young-block
  `tableauDim` multiples, from the labeled matching eigenbasis assumed in the
  paper statement.
- Lemmas 5.18--5.21 expose the active tableauDim spectral-bridge route used by
  Theorem 4.8.
- Lemmas 5.11 and 5.13 are now complete for the intended matching sizes in both
  parity cases.  Lemma 5.19 now proves the concrete Young matrix-coefficient
  family, same- and distinct-shape orthogonality, global linear independence,
  right-convolution scalarity, the `h / d` values, and the matching-error
  quadratic-form identity.  The one-box Young-lattice differential recurrence,
  upward tableau-dimension recursion, tableau sum-of-squares identity, and
  coefficient-index cardinality theorem are now proved internally.  Thus the
  concrete basis, block components, energies, and Parseval are unconditional.
  The faithful A.3 subspace equality is now proved internally and gives the
  exact `l2DistSqToU1` complementary-energy identity by an internal `sInf`
  argument.
- A.1 now has the faithful Young-action axiom type.  A.2 supplies faithful
  content-action data together with its trace/scalar payload.  A.3 proves the
  faithful one-row-plus-standard subspace equality internally.  Lemma 5.19 now
  proves the final global weighted matching identity in both parity cases.
- Appendix A exposes explicit marker axioms for A.1 and A.2.  Lemma 5.19
  combines those markers with internal A.3 and the proved scalarity identities to
  produce the even/odd spectral-model theorem wrappers
  `spectralBlockModelInputWithDim_even_from_appendixA` and
  `spectralBlockModelInputWithDim_odd_from_appendixA`.

## Internal Progress

- Definitions 5.1--5.5 expose the numbered tableau-preliminary interfaces.
- Lemma 5.1 exposes the concrete tableau-coordinate Coxeter model.
- Lemma 5.2 is proved internally for explicit diagonal content operators.
- Lemma 5.3 proves standard-tableaux adjacent-swap connectedness internally.
- Lemma 5.4 proves the fixed two-step tableau branching equivalence.
- Lemma 5.6 proves the concrete coordinate form of one-box deletion unitarity.
- Lemma 5.7 proves deletion/content compatibility and earlier-adjacent
  coefficient preservation.
- Lemma 5.10 proves the genuine recursive sign-pattern multiset cardinalities,
  zero multiplicity, and even/odd high multiplicities.
- Lemma 5.11 proves the concrete matching-cube action, sign-projection wrappers,
  the full signed-child orthogonal decomposition, and the recursive canonical
  even labeled eigenbasis with exact label multiplicities. Arbitrary perfect
  matching transport is proved by explicit conjugation and isometry.  The
  canonical and arbitrary near-perfect-matching odd bases and their exact label
  multiplicities are proved as well.
- Lemma 5.12 proves the matching-character local truncation calculation.
- Definition 5.22 proves the low/high matching idempotent algebra.
- Lemma 5.14 proves local truncation as convolution.
- Lemma 5.15 proves the finite-average local rejection identities, and
  Definition 5.29 proves coefficient centrality of the actual averaged high
  matching element plus one-block scalarity for a supplied Young action model.
- Lemma 5.18 proves weighted-sum spectral-gap algebra from block scalar lower
  bounds.
- Lemma 5.19 proves the finite orthogonal-component weighted-energy identity;
  concrete Young matrix coefficients and synthesis blocks; right convolution
  on matrix coefficients; scalarity of the actual averaged element on each
  concrete block; even/odd `h / tableauDim` scalar formulas; normalized
  same- and distinct-shape orthogonality; global linear independence; and the
  matching projection error as the averaged-convolution quadratic form.  Its
  internal Young-lattice proof gives the exact global coefficient-index
  cardinality equality, so it unconditionally constructs a concrete basis,
  block components and energies, their pairwise orthogonality, Parseval, and
  the A.3 complementary-energy formula for `l2DistSqToU1`.  It also proves
  `S05_matchingAverageScalarity_concrete_even` and
  `S05_matchingAverageScalarity_concrete_odd`; its active paper wrappers now
  assemble external Appendix A.1--A.2 and internal A.3 into
  `SpectralBlockModelInputWithDim`.
- Lemmas 5.20 and 5.21 prove the even and odd algebraic spectral bridges from
  explicit spectral-block-model hypotheses plus finite certificates.
- Lemmas 5.23, 5.25, and 5.27 prove the finite `z`, even `h`, and odd `h`
  certificates.

## Appendix A Boundary

The following remain external inputs rather than Lean-proved representation
theorems:

- A.1 Young orthogonal realization.
- A.2 Jucys--Murphy content spectrum.

A.3 degree-one Young-block identification is proved internally in
`S05_Int_DegreeOneYoungBlock.lean`.

Standard-tableaux connectedness is proved internally as Lemma 5.3 in
`S05_Lem5_03_ConnectednessOfStandardTableaux.lean`.

The Appendix A files add only the A.1/A.2 external marker axioms.  Lemma 5.19
proves matching-average scalarity internally and assembles those two external
ingredients together with internal A.3 into the spectral model wrappers.  The current Section 5
tableau-count dimension route also no longer registers the older `youngDim`
dimension-branching instances.

For the concrete route, the coefficient-index cardinality equality and the
standard-tableau sum-of-squares identity are proved internally from the
Young-lattice differential relation.  A.3 now proves the faithful concrete
subspace equality, and its exact distance consequence is proved internally.
The even and odd weighted matching-energy identities are also proved internally;
the remaining external representation boundary is exactly A.1--A.2.
