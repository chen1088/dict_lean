# Dictatorship Testing on the Symmetric Group

Lean 4 + Mathlib formalization accompanying the dictatorship-testing paper.
Reusable foundations live in the separate `AlgebraicLibrary`; paper-facing
modules remain under `DictatorshipTesting` and are numbered from the compiled
paper. Paper-specific implementation machinery lives in `S##_Int_*` and
`Defs/S##_IntDef_*` modules.

Each edge between numbered nodes in `docs/dependency-data.js` is mirrored by a
direct import in the corresponding paper-facing Lean module. Large proof bodies
may remain in internal modules, but the numbered imports expose the paper's
logical route explicitly.

## Build

```bash
lake exe cache get
lake build DictatorshipTesting
```

The first command downloads Mathlib's compiled cache and normally only needs to
be rerun after dependency changes. Lake caches each compiled module as an
`.olean` under `.lake/build`; `lake build DictatorshipTesting` automatically
builds the `AlgebraicLibrary` modules it needs and reuses every unchanged
artifact. Run `lake build AlgebraicLibrary` separately only when validating the
whole reusable library. The job count printed by Lake includes dependencies it
checked; only lines beginning with `Built` indicate actual recompilation.

Focused builds use the module target, for example:

```bash
lake build +DictatorshipTesting.Paper.S05_Thm5_02_YoungOrthogonalAction:olean
lake build +DictatorshipTesting.Paper.S05_Prop5_16_AveragedRejectionOnYoungBlocks:olean
```

## Paper Maps

- `paper_numbering_map.md`
- `DictatorshipTesting/Paper/SECTION1_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION2_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION3_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION4_FILE_MAP.md`
- `DictatorshipTesting/Paper/SECTION5_FILE_MAP.md`
- `DictatorshipTesting/Paper/DEFINITION_FILE_MAP.md`

Section 5 contains 12 numbered definitions and 20 numbered results. Reusable
definitions link directly to their `AlgebraicLibrary` modules instead of going
through paper-side forwarding files. Paper-specific grouped definitions retain
letter-suffixed files only when those files contain substantive definitions or
proofs.

The representation-theory results are part of Section 5:

- Theorem 5.2 constructs the Young orthogonal action.
- Theorem 5.3 proves the Jucys--Murphy content action.
- Lemma 5.9 identifies the degree-one Young blocks.

The concrete regular block decomposition and global weighted matching identity
are proved internally and exposed as Lemma 5.8 and Proposition 5.16. The operational
finite-seed tester, independent repetition, small-rank exhaustive tester, and
dimension-free amplification are also formalized.

The shortened paper contains 15 numbered definitions and 33 theorem-like
statements. Definition 4.1, Proposition 4.2, and the combined Section 5 results
keep their proof components in the corresponding numbered modules.

## Assumptions

The only named mathematical assumptions are the two Section 2 literature
inputs:

- `booleanU1_dictator_classification_input`
- `fknStability_input`

See `ASSUMPTIONS.md` for references and audit commands.

## Dependency Viewer

The static dependency viewer is under `docs/` and can be hosted with GitHub
Pages. Its graph data are in `docs/dependency-data.js`.
