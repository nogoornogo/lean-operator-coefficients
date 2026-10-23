# Constructed Shared Connections

The implementation constructs shared selected-field dictionaries from concrete
maps, lifts the same dictionaries to statistics-correct mixed powers and jet
syntax, and preserves full-relation input evaluations and inverse recovery.
The reader-facing [dossier](../../proof/current/inputs/Physics/FIELD_CONNECTIONS.md)
owns the statements and hypotheses.

## Implemented Stages

| Planned stage | Artifact |
| --- | --- |
| Field description | Existing typed species/actual representations retained; separate internal-dual and Weyl factors in `SelectedFields`; basis coordinate presentation for jets |
| Selection and exactness | Stable kernels, common fixed constraints, boundary adapter, derived stability from realized images, two-sided inverse criterion, subgroup/coordinate transports |
| Interaction symmetry | Generic dual pairing, arbitrary multilinear restriction, fixed-vacuum insertion, all-degree exterior/symmetric coefficient equivalence and evaluation |
| Existing-input adapters | Actual field-to-jet/mixed-algebra maps; exact full-relation preimages; quotient-image equivalence; selected coefficient equivalence and recovery |
| Model validation | Boundary and mass-kernel dictionaries, full density/paper connection, S3 positive coefficient and symmetry, structural negative controls |

No existing theorem, public input type, compatibility stub, dependency pin,
proof limit or axiom allowance is changed. The authorized
[README follow-up](readme-verification.md) adds the optional connection to its
input/model maps without changing the selected main claims.

## Model-Specific Results

The SU(6) dictionaries carry the SM gauge and residual circle action jointly.
The left fifteen retains Q and ec, the right twenty its up-color component,
and the right six its color and weak components. Their component maps and
exactness proofs come from the existing branching construction. The exact `sterileDictionary` singlet
amplitude remains separate from the ten-species SM/Higgs coefficient alphabet.
Right Weyl spin and internal duality have separate definitions. The fixed
brane vacuum reconstructs the existing wedge interaction exactly.

The lepton-parity example constructs its dictionary from the actual spectator
mass and proves agreement with the earlier radical equivalence. It reuses
the existing physical species/Weyl regrouping and the same nonzero Yukawa
tensors, nonzero spectator mass and B1 input. Both main models expose jet
coordinate dictionaries for a supplied direction action; an interacting full
relation module must still be generated or supplied on that actual source.

The scalar/Weyl example implements a genuine sign change of the odd fields
with unchanged bosons/directions. Its induced algebra map reexpresses the
complete generated equations, including both Yukawa parameters. A selected
even source retains the exact full preimage. A density p-p has only the IBP
range before and after this connection. The paper-syntax coefficient map is
composed with the new input equivalence and preserves evaluation.

The S3 kernel example uses the same inverse-map construction and transports
the known positive qque functional and exchange symmetry. Its existing
uniform-flavor obstruction remains in force.

## Boundaries And Completion

No analytic mixed-mode problem or new branching problem was needed. The
examples are algebraic field dictionaries, not a fitted particle model.
No counterexample to a stated shared theorem was found. Expected negative
controls demonstrate why each exactness/symmetry/selection condition is needed.
The frozen implementation and validation endpoint is complete. Final acceptance
commands and residual import-style warnings are recorded in
[verification](verification.md). The completed child is integrated into its
recorded parent; [integration verification](integration-verification.md)
records the merged-state checks and retained boundaries.
