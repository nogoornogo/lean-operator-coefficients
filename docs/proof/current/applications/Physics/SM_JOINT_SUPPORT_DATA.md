# Executable SM metadata and actual support

`SMJointSupportData.dataSupport_iff` proves equivalence of the executable
metadata support predicate and `SMJointContentSupport.Supports` for every
signed three-generation content and weak degree. `higgsDataSupport_iff` and
`original_ql_iff` retain arbitrary Higgs bidegrees and the exact scalar cyclic
q/l residual/hypercharge conditions. These are actual coefficient-space
statements, with no Weyl, numerical-rank or supplied occurrence premise.

## Data and actual presentation

[SMCoreSourceData](../../../../../Physics/StandardModel/Operators/SMCoreSourceData.lean)
constructs `coreData` directly from the species number and exterior degree.
It uses the proved mathematical syntax functions for all signed core families,
including complementary and overflow degrees. `corePresentation` retains the
actual representation equivalence while placing this executable data in the
outer `expression` field. Its dependent dispatch chooses equivalences only.
The generic [reexpression helper](../../../../../Math/RepresentationTheory/JointSourceReexpression.lean)
uses ordinary equality transport; it adds no decomposition assumption.

[SMJointSupportData](../../../../../Physics/StandardModel/Operators/SMJointSupportData.lean)
uses numeric compact occupation indices and the existing mathematical data
composition. `expressionData_eq` identifies that expression with the new
actual presentation. `dataSupport_presented_iff` reindexes all occupations in
both directions. Both the new and old presentations decompose the same full
joint source, so the two applications of `JointContentPresentation.allowed_iff`
give `dataSupport_iff` without expanding the old dependent expression projection.
Color, weak and the two Lorentz factors stay on one joint branch throughout.

The executable data definitions do not access the noncomputable equivalence
fields. The semantic presentations can remain noncomputable, and the old
general `Decidable` functions are unchanged. This module provides an executable
data layer and ordinary semantic proofs, not a generic compiled support solver.
SM metadata composition visits the fixed ten-species/three-generation slots
and finite core templates; it retains sum/tensor syntax rather than enumerating
the Cartesian product of branches.

## Ordinary consumers and trust

[SMJointSupportDataExamples](../../../../../Physics/StandardModel/Operators/SMJointSupportDataExamples.lean)
checks generic supplied-component transport and original-space reconstruction,
plus explicit mixed d,u,Q,L/h=d=0 and Q18/h=0,d=6 source choices. Their allowances
use existing algebraic family results, then the new interface. The independent
chirality exclusion gives the Q/conjugate-Q negative. No decision tactic,
Boolean-reflection proof or external numerical certificate is added. Existing
mathematical/family proofs are reused as already checked lemmas.

The [persistent audit](../../../../../Physics/StandardModel/Operators/Audit/AuditSMJointSupportData.lean)
checks all new named Physics interfaces/consumers and imports the two-declaration
Math helper audit. Only `propext`, `Classical.choice` and `Quot.sound` are allowed
transitively; there are no exceptions. Source review separately enforces the
no-computational-support-proof policy, which an axiom audit alone cannot check.

Fresh importing consumers and runtime metadata diagnostics are checked under
120 seconds/10 GiB, including ordinary positive/negative cases and supplied
large-content component transport. These measurements cover named uses, not
arbitrary search or universal resource complexity. An allowed coefficient is
not a generated interaction or a rate. Other dictionaries, derivatives/EOM/IBP
and UV realization remain outside this result.

See the [revision and verification record](../../../../topics/sm-support-evaluator-feasibility/data-connection-results.md)
for measurements, the superseded resource-stop route, full build and remaining
performance boundaries.
