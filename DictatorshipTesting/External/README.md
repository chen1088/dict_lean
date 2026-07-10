# External formalization layer

This folder contains formalization attempts for the paper's external Appendix A
inputs.

Paper-facing files in `DictatorshipTesting/Paper/AppA_*` should eventually
become thin wrappers importing proofs from this folder.  Work here should not
hide incomplete arguments behind broad axioms: if a proof is incomplete, record
the exact missing bridge instead of packaging it as a new external theorem.

Current Appendix A targets are A.1 Young orthogonal realization, A.2 the
Jucys--Murphy content spectrum, and A.3 degree-one Young-block identification.
Their paper-facing declarations remain explicit external inputs while internal
formalizations are developed.

Standard-tableau connectedness is no longer part of this external layer.  It is
proved internally as Section 5 Lemma 5.3.  Matching-average scalarity remains
isolated separately as the Section 5 input
`S05_matchingAverageScalarity_from_young_model_input`.
