# External formalization layer

This folder contains formalization attempts for the paper's external Appendix A
inputs.

Paper-facing files in `DictatorshipTesting/Paper/AppA_*` should eventually
become thin wrappers importing proofs from this folder.  Work here should not
hide incomplete arguments behind broad axioms: if a proof is incomplete, record
the exact missing bridge instead of packaging it as a new external theorem.

Current focus:

- `AppendixA/A04_TableauxSwapConnectedness.lean` proves A.4.  It connects any
  two finite linear extensions by explicit adjacent swaps of incomparable
  elements, specializes the construction to box orders of standard Young
  tableaux, and transports the resulting path to valid adjacent tableau swaps.
  The paper-facing A.4 file is a theorem wrapper around this proof; A.4 is no
  longer an axiom.
- Matching-average scalarity is not part of A.4.  It is isolated in Section 5
  as `S05_matchingAverageScalarity_from_young_model_input`, which depends on
  the A.4 connectedness statement and the trace/scalar data from the Young
  model.
