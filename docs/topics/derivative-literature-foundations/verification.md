# Verification By Milestone

## A — Generated Higgs And Actual Symmetry

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditDerivativeLiteratureFoundations Physics.FieldTheory.Jets.Audit.AuditLiteratureFoundations
LEAN_NUM_THREADS=2 lake build
```

The focused gate passes 3733 jobs and all 183 namespace-wide strict
transitive declaration checks: 118 Math and 65 Physics. The audits include
definitions, instances and generated helpers, reject forbidden layer
imports, require every namespace inventory to be nonempty and permit only
propext, Classical.choice and Quot.sound. All seven new source modules and
both audits are registered in the appropriate aggregates.

The serialized full build passes 7712 jobs. These gates used the intended
thread environment setting, the inherited 16 GiB per-process address-space
guard and default Lean elaboration limits, with 180/540-second focused/full
ceilings. Subsequent source inspection showed that Lean 4.35 does not read
`LEAN_NUM_THREADS`; the earlier claim of an enforced two-thread shell was
incorrect. The final gate below uses explicit `-j2` compiler arguments.
No proof limit is raised. New source warnings are repaired; inherited module-system
advisories remain. Intermediate normalization, coercion and unfolding
errors were repaired before the gates. They are not mathematical stops.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py --pending-topic derivative-literature-foundations
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes 2218 modules. Topic navigation passes 161 topics with the
single explicit pending exception, because B and C are still active.
Metadata, local links and whitespace checks pass. The link checker is
unchanged and runs with its required Git subprocess permitted. The
Higgs dossier, actual source signatures, assumptions, bibliography and
coverage row agree on the gaugeless/global-action scope.

This is a verified milestone, not the final topic stop. B and C continue
under the frozen contract. No master merge or remote update is authorized.

## Final A–C Gate

```sh
lake build Math.RepresentationTheory.Audit.AuditDerivativeLiteratureFoundations Physics.FieldTheory.Jets.Audit.AuditLiteratureFoundations
lake build
```

The focused gate passes 3934 jobs and 441 strict transitive declaration
checks: 286 Math and 155 Physics. These are namespace inventories, including
the reused two-sided closure declarations, not a count of new theorems.
Every new source is covered, with the same three-axiom allowance and layer
import rejections. No proof parameter admits a literature completeness count.

The root package's `weakLeanArgs` now passes `-j2` explicitly to each root
module compiler without changing proof options, dependency pins or build
traces. Direct focused invocations use `lake env lean -j2`. The setting does
not bound Lake's concurrent compiler count or external package arguments.
The 16 GiB address-space guard, 180/540-second ceilings and default elaboration
and kernel limits are retained. Early thread/allocation failures and the
component-membership kernel timeout were development diagnostics. Explicit
seed normalization and named span/closure lemmas repair the accepted proof;
no budget or axiom allowance is raised to force success.

The exact scalar diagnostic is rerun and retains source sizes 1/20/305,
EOM/IBP ranks 0/11/235 and infinitesimal constrained dimensions (1,0,1).
It remains supplementary; only the new degree-zero actual image is completely
certified here. Positive-degree counts and C4/C5 completeness remain partial.

The serialized full build passes 7722 jobs, including all three aggregates.
All 17 new source modules and the two persistent foundation audits are
registered. New source warnings are repaired; inherited module-system
advisories remain. No Lean proof changes follow this final full-build gate.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes 2228 modules. Default navigation passes all 161 topics and
161 outcomes without a pending exception. Portable metadata and whitespace
checks pass. The unchanged link checker passes with its Git subprocess
permitted. Source signatures, assumptions, bibliography, usage and coverage
are reviewed against the scoped results. The bounded endpoint is settled
on its topic branch; no master merge, branch deletion or push is performed.

## Common Input Guide Follow-Up

The existing derivative input guide now lists the Higgs and paired Weyl
constructors alongside the graded, commutative EOM and supplied-relation
routes. It records the packaged proof obligations, spectator and symmetry
scope, and the optional finite-carrier coordinate certificate. The generated
input guide links back to that common choice of routes. The input types,
Lean sources and dependency pins are unchanged.

```sh
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Navigation, portable metadata, local links and whitespace checks pass.
The existing checker runs unchanged with its Git subprocess permitted.
This follow-up changes documentation only; no Lean build or axiom audit is
rerun, and the preceding proof baseline is retained.

## Literature Recheck Gate

The user-directed [frozen recheck](literature-recheck-plan.md) proceeds
through all six cases and the [report](literature-recheck.md) records each
terminal result. The six primary pinned PDFs and selected equation/table
text were reopened; [inspection locations](references.md#renewed-primary-source-inspection)
record their conventions and limits.

```sh
lake build Physics.FieldTheory.Jets.Audit.AuditLiteratureRecheck
lake build
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
```

The focused build passes 3943 jobs. Its persistent namespace inventories
check all 28 new consumer declarations and generated helpers, split by
case as 4/1/5/6/10/2. Strict transitive axiom checks permit only propext,
Classical.choice and Quot.sound, reject model-layer imports, and require
all six inventories to be nonempty. The consumer and audit are registered
in Physics.lean. Definitions as well as theorems are included; this is not
a count of new independent mathematical results.

The serialized full build passes 7724 jobs, including Math, Physics and
GUT aggregates and the earlier audits. Compiler -j2, the 16 GiB per-process
address-space guard, 180/540-second ceilings and default elaboration/kernel
limits are retained. Intermediate scalar-normalization and linear-combination
diagnostics were repaired; the finite Pauli component identity succeeds
without a fallback or increased limit. New files have no warnings; inherited
module-system advisories remain. No Lean source changes follow this gate.

Both exact scripts pass and reproduce the earlier outputs. C1 gives
one-species off/on dimensions 1/0 and two-species on-shell sequences
(1,1,0)/(1,1,1). C2 gives source sizes 1/20/305, EOM/IBP ranks 0/11/235
and infinitesimal constrained dimensions (1,0,1). These diagnostic values
are not Lean premises or substitutes for the missing source/group bridges.

The renewed source statements, report, dossier, assumptions, bibliography
and coverage distinguish the exact C3 input/relation, C5 current conservation
and C4 raw-probe rejection from the still unproved complete bases.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes 2230 modules; default navigation passes 161 topics with 161
outcomes and no pending exceptions. Portable metadata, local links and
whitespace checks pass. The unchanged link checker runs with its required
Git subprocess permitted. The bounded recheck is settled on the existing
topic branch with the verified changes committed. No master integration,
branch deletion or remote operation is performed.

## Portfolio Closure

The user closed this verification topic before the separately authorized
C1/C2 completeness implementation. This closure changes documentation only.
No Lean build was rerun for the closure; the additional input gate retains
its own verified baseline. Topic navigation, metadata, local-link and
whitespace checks pass. Existing partial boundaries remain explicit and
no master integration is performed.

## Additional Input Verification Gate

The [four-part plan](extended-checks-plan.md) and [report](extended-checks.md)
cover actual Lorentz old/new input controls, full-relation presentation
changes, additional complete C1 sectors and supported reality. Remaining
positive-degree C1/C2 completeness obligations have explicit partial stops;
all four items were executed without stopping the queue early.

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build Math.RepresentationTheory.Audit.AuditExtendedDerivativeChecks Physics.FieldTheory.Jets.Audit.AuditExtendedDerivativeChecks
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
```

Here the disposable wrapper sets a 16 GiB per-process address-space limit
and execs its arguments. Explicit compiler -j2 and default elaboration/kernel
limits are retained. CPU affinity also bounds Lake's runtime scheduling.
An earlier multi-target build failed to create runtime threads; it did not
produce a theorem result. The bounded rerun passes without raising any cap.
Intermediate type, finite-product and coefficient-normalization diagnostics
were repaired within the stated limits.

Focused verification passes 3915 jobs. All seven new source namespaces have
strict transitive declaration inventories, including instances, definitions
and generated helpers: Math counts 32/77/11/6/29 and Physics counts 20/32,
207 total. Only propext, Classical.choice and Quot.sound are allowed; wrong
source-layer imports and empty inventories fail. These are declaration
checks, not 207 independent new mathematical results. The nine new source
and audit modules are registered in the appropriate aggregates.

The serialized full build passes 7737 jobs, including Math, Physics, GUT and
the strict audits. New modules have no proof/linter warnings; direct mathlib
imports in the semilinear and real-dimension helpers retain module-system
advisories, alongside existing imported advisories. No Lean source changes
follow this gate. Published input definitions and dependency pins are unchanged.

Both exact standard-library Python diagnostics pass. C1 verifies the
remaining finite dimensions and explicit representatives complete each
nonzero finite quotient. C2 retains source sizes 1/20/305 and finite ranks
0/20/304 after infinitesimal constraints; the literal phi^4 and K squared
vectors increase rank by one and complete the corresponding finite spaces.
No script value is a Lean premise or full-group/actual-source certificate.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes 2243 modules. Default navigation passes 161 topics with 161
outcomes and no pending exception. Portable metadata passes 1222 documents
and evidence files. Local links pass 1230 Markdown files, 7862 local links
and 153 heading fragments with zero errors; whitespace checks pass. The
unchanged link checker runs with its required Git subprocess permitted.
The topic, dossiers, assumptions, usage guides, bibliography and coverage
agree on the proved scope and partial stops. The settled unmerged outcome
is recorded and the reviewed changes are committed on the topic branch.
No master merge, branch deletion or remote operation is included.

## Nonderivative Input Recheck Gate

The user-directed [Z1–Z5 plan](nonderivative-recheck-plan.md) and
[report](nonderivative-recheck.md) cover actual original input coefficients,
both inverse/evaluation laws, concrete Bose/Fermi/mixed statistics, empty
finite-local extra relations and nonderivative targets in the actual scalar
and Higgs EOM inputs. Primary nonderivative term locations were reinspected
as recorded in the [source register](references.md#nonderivative-input-inspection).

```sh
lake build Math.RepresentationTheory.Audit.AuditNonDerivativeInputChecks Physics.FieldTheory.Jets.Audit.AuditNonDerivativeModelChecks
lake build
```

The focused build passes 3934 jobs and 84 namespace-wide strict transitive
declaration checks: 62 Math and 22 Physics. The Math inventory covers the
entire source namespace, including its two supporting module instances;
the Physics inventories are 7/15 for Scalar/Higgs. Definitions, instances
and generated helpers are included; these are not 84 independent new
mathematical results. The
audits require nonempty inventories, reject wrong-layer imports and permit
only propext, Classical.choice and Quot.sound. All four new source/audit
modules are registered in Math.lean or Physics.lean.

The serialized full build passes 7728 jobs including all three aggregates.
Both gates retain explicit compiler -j2, the 16 GiB per-process address-space
guard, 180/540-second ceilings and default elaboration/kernel limits.
Intermediate type-inference and repeated-odd normalization errors were
repaired within those bounds. New modules have no warnings; inherited
module-system advisories remain. No Lean source changes follow this gate.

The checked old input is the actual original exterior/symmetric coefficient
type, not an assumed coefficient presentation. The finite-local control
reuses a proved complete local scalar basis. Concrete coefficient values
and the interacting scalar's rejected value are Lean proofs, not script
outputs. No new numerical diagnostic is required for these symbolic checks.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes 2234 modules; navigation passes all 161 topics with 161
outcomes and no pending exceptions. Portable metadata, local links and
whitespace checks pass. The existing link checker runs unchanged with its
required Git subprocess permitted. Statements, input guides, dossier,
assumptions and literature coverage agree on zero-degree off-shell recovery
versus additional EOM constraints. All Z1–Z5 outcomes are settled and the
verified work is committed on the existing topic branch. No master merge,
branch deletion or remote operation is performed.
