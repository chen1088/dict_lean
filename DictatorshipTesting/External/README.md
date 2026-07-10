# External formalization layer

This folder contains formalization attempts for the paper's external Appendix A
inputs.

Paper-facing files in `DictatorshipTesting/Paper/AppA_*` should eventually
become thin wrappers importing proofs from this folder.  Work here should not
hide incomplete arguments behind broad axioms: if a proof is incomplete, record
the exact missing bridge instead of packaging it as a new external theorem.

Current focus:

- `AppendixA/A04_TableauxSwapConnectedness.lean` starts the A.4 connectedness
  input by isolating the elementary finite-poset/list layer and exposing the
  standard-tableau adjacent-swap connectedness statement.  The paper-facing A.4
  axiom is not yet replaced because the specialization from linear extensions
  to standard tableaux is still unfinished.
- Matching-average scalarity is not part of A.4.  It is isolated in Section 5
  as `S05_matchingAverageScalarity_from_young_model_input`, which depends on
  the A.4 connectedness statement and the trace/scalar data from the Young
  model.
