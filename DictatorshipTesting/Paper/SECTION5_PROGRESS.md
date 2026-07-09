# Section 5 Progress

Source checked: `../dictatorship_testing_soda27_latest.tex`.

## Spine Status

- Section 5 now has 49 theorem-like numbered statements when counting only
  `definition`, `lemma`, `proposition`, `theorem`, and `corollary`
  environments.
- Section 5 paper-facing Lean file count is 49.
- Appendix A has 4 numbered external-input statements and 4 Lean-facing files.
- No two Section 5 paper-facing Lean files share the same paper statement
  number.
- Interface definitions formerly bundled under Lemmas 5.23, 5.25, and 5.29 are
  now exposed as Definitions 5.25--5.28, 5.31--5.32, and 5.37.
- The regular Young-block decomposition assembly lemma is in Section 5:
  `S05_Lem5_41_RegularYoungBlockDecomposition.lean`.
- The degree-one Young-block input is in Appendix A:
  `AppA_LemA_03_DegreeOneYoungBlockIdentification.lean`.

Detailed maps:

- `SECTION5_FILE_MAP.md`
- `APPENDIX_A_FILE_MAP.md`
- `DEFINITION_FILE_MAP.md`

## Latest Checkpoint

- Definition 5.8 is now only the Young-block index interface.
- Definitions 5.9 and 5.10 expose the Young-block energy profile and the
  `U_1`-compatible block profile.
- Definitions 5.25 and 5.26 expose the even and odd matching eigenvector
  predicates.
- Definitions 5.27 and 5.28 expose the even and odd matching-restriction scalar
  inputs.
- Definitions 5.31 and 5.32 expose the even and odd local-truncation trace
  inputs.
- Definition 5.37 exposes the Young-basis scalar commutant input.
- Lemma 5.18 coordinate-level deletion-fiber intertwining is proved:
  `S05_Lem5_18_deletionCoordinateMap_youngAdjacentOperator_intertwines`.
- Lemma 5.29 has proved matching eigenvalue preservation under one-edge
  projections, support-selected one-edge projections, and simultaneous matching
  sign projections.
- Definition 5.34 has proved low/high matching idempotent identities, zero
  cross-compositions, and the low-plus-high decomposition identity.
- Lemma 5.36 proves the finite-average/high-idempotent part of central averaged
  rejection.
- Lemmas 5.40--5.43 expose the active tableauDim spectral-bridge route used by
  Theorem 4.10.
- The remaining representation-theoretic frontier is the spectral-block model
  input supplied by Appendix A.
- Appendix A exposes explicit marker axioms for A.1, A.2, A.3, and A.4. Lemma
  5.41 consumes those markers to produce the even/odd spectral-model theorem
  wrappers `spectralBlockModelInputWithDim_even_from_appendixA` and
  `spectralBlockModelInputWithDim_odd_from_appendixA`.

## Internal Progress

- Definitions 5.1--5.5 expose the numbered tableau-preliminary interfaces.
- Lemma 5.6 exposes the concrete tableau-coordinate Coxeter model.
- Lemma 5.7 is proved internally for explicit diagonal content operators.
- Lemma 5.14 proves the fixed two-step tableau branching equivalence.
- Lemma 5.17 proves the concrete coordinate form of one-box deletion unitarity.
- Lemma 5.18 proves deletion/content compatibility and earlier-adjacent
  coefficient preservation.
- Lemma 5.23 proves the tableau-count size identities for the sign-pattern
  multisets.
- Lemma 5.29 proves the concrete matching-cube action and sign-projection
  wrappers around the matching eigenvector predicates.
- Lemma 5.30 proves the matching-character local truncation calculation.
- Definition 5.34 proves the low/high matching idempotent algebra.
- Lemma 5.35 proves local truncation as convolution.
- Lemma 5.36 proves the finite-average local rejection identities; centrality on
  Young blocks remains representation-layer input.
- Lemma 5.40 proves weighted-sum spectral-gap algebra from block scalar lower
  bounds.
- Lemma 5.41 assembles Appendix A inputs into `SpectralBlockModelInputWithDim`.
- Lemmas 5.42 and 5.43 prove the even and odd algebraic spectral bridges from
  explicit spectral-block-model hypotheses plus finite certificates.
- Lemmas 5.45, 5.47, and 5.49 prove the finite `z`, even `h`, and odd `h`
  certificates.

## Appendix A Boundary

The following remain external inputs rather than Lean-proved representation
theorems:

- A.1 Young orthogonal realization.
- A.2 Jucys--Murphy content spectrum.
- A.3 Degree-one Young-block identification.
- A.4 Connectedness of standard tableaux.

The Appendix A files add only the A.1/A.2/A.3/A.4 external marker axioms.
Lemma 5.41 has no standalone external input; it is proved by assembling those
markers into the spectral model wrappers.  The current Section 5 tableau-count
dimension route also no longer registers the older `youngDim`
dimension-branching instances.