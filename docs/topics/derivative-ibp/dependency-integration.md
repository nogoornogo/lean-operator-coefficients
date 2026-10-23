# Physlib / Lean v4.35.0 Connection

Status: completed; dependency child integrated into the topic parent and reverified.
The [carrier/projection pilot](carrier-pilot.md) owns the current repair and
verification. The [initial repair](compatibility-repair.md) and
[ScalarBlock stop](conversion-stop.md) retain superseded checkpoint evidence.
The later [scalar implementation](implementation-plan.md) is a separate proof
phase using these unchanged pins.

## Endpoint And Authority

The user authorized Physlib with Lean v4.35.0 and compatible dependency changes,
with exact revisions frozen after verification. This checkpoint connects the
dependency and preserves existing proofs; derivative/IBP completeness remains
outside its endpoint.

- Parent working branch and integration target: `proof/derivative-ibp`.
- Bounded child branch: `audit/derivative-ibp-physlib-435`.
- Parent exception: this child may branch from and merge into the unmerged
  parent at agent discretion. It never authorizes a master merge.
- Acceptance: focused builds, persistent strict transitive audits, full
  `lake build`, layout, links, topic index, metadata and diff checks;
  synchronized optional docbuild pins and merged-parent verification.
- Stop for new foundational mathematics, audit exceptions, a toolchain newer
  than v4.35.0 or substantial dependency patches. No dependency checkout is
  patched. No master merge or remote push is authorized.

## Pinned Dependency Set

Root and optional docbuild both use `leanprover/lean4:v4.35.0`.
Exact root and transitive revisions are in the two Lake manifests.

| Dependency | Selected revision | Reason |
| --- | --- | --- |
| Mathlib | [fixed revision](https://github.com/leanprover-community/mathlib4/commit/074063781836922cb02701cd12943c9f51731afa) | TauCeti's compatible v4.35.0 pin |
| TauCeti | [fixed revision](https://github.com/TauCetiProject/TauCeti/commit/1f9b4414105d86e487a4ac4c3d3397076a44d0d2) | v4.35.0 source, including required root-system APIs |
| Physlib | [fixed revision](https://github.com/leanprover-community/physlib/commit/5bbbb30d08b8e151406a10affbc8a369b74b32c6) | The surveyed v4.35.0 snapshot |
| Optional doc-gen4 | [v4.35.0 revision](https://github.com/leanprover/doc-gen4/commit/0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae) | Matching compiler release |

Physlib's own Mathlib release pin differs from the shared pin above.
Compatibility must be established by actual builds of the combined closure.
The initial imported audit passed in isolation; the subsequent
[namespaced repair](compatibility-repair.md) resolves the aggregate collision.
The carrier/projection repair closes the later consumer failures in focused
strict audits and the full project build now passes. The installed
Mathlib, TauCeti and Physlib checkouts match the root manifest and are clean.
Root/docbuild shared dependency revisions match. Routine builds must not
run an unrestricted `lake update`.

## Narrow Physlib Boundary

The persistent [connection audit](../../../Math/Audit/AuditPhyslibAlgebraConnection.lean)
imports `PhyslibAlpha.Mathematics.ExteriorAlgebra` and the local
[namespaced symmetric fragment](../../../Math/LinearAlgebra/PhyslibSymmetricDerivations.lean),
together with TauCeti symmetric functoriality. It permits only that exterior
module in the external Physlib closure and requires the three compatibility
modules to be present. Twelve generator, Leibniz, commutation, covariance and
representation declarations are checked transitively against `propext`,
`Classical.choice`, `Quot.sound` only. The same semiring/module hypotheses
are preserved in the adapted fragment.

The original attempt imported both upstream modules directly. This failed
because both libraries define root symmetric functoriality names. The current
fragment retains sections D/E under `Math.PhyslibSymmetric`, with explicit
calls replacing upstream dot notation. Copyright, authorship, Apache-2.0 notice
and exact external revision are retained in the source header. No installed
dependency is edited. The larger external SM jet and analytic IBP packages
remain uncertified; this is no derivative/IBP completeness theorem.

## Existing-Proof Compatibility Port

| API change | Retained implementation |
| --- | --- |
| `TauCeti.ContRepresentation` unitary/character declarations | Root `ContRepresentation` declarations; congruence under `ContinuousLinearEquiv` |
| Exterior and symmetric diagonal-basis, trace and coordinate lemmas | Current `Module.Basis` declarations, with explicit exterior `Basis` import |
| `exteriorPower.topEquiv` and determinant-action lemmas | `Module.Basis.exteriorPowerTopEquiv`, basis/top and `LinearMap`/finrank determinant lemmas |
| `LogOneAdd.Inverse` | `Logarithm.Inverse`; `log (1 + T)` and `eventually_log_exp` |
| Logarithm chart analyticity | `log` at `A`, replacing the old function at `A - 1`; inverse near one |
| Fundamental-group representation | Explicit `FundamentalGroup.fromPath` / `toPath` wrapper |
| Set carriers and conjunction | Set-builder syntax and `Set.ofPred_and` |
| `contDiff_apply` argument `E` | Explicit dependent family `F'` |

These changes retain the existing assumptions and mathematical conclusions.
The E6 chart/log dossiers use the current API while retaining their original
verification counts as historical evidence. No E6 global identification or
new physical endpoint is introduced. The inverse audit helper is now
`matrix_exp_log_near_one`.

Two concrete transport/equivalence files retain bounded
`synthInstance.maxHeartbeats = 200000`: `SupportedQuotient` and
`MultiplicityUnitaryCentralizer`. A common abstract product nonzero lemma
replaces repeated concrete proof expansion in the four/eight-family
coefficient decompositions; their statements and hypotheses are unchanged.
Their existing strict consumer audits cover the helper transitively.

## Concrete Mass-Type Repair

Two concrete SU(6) mass transports hit kernel timeouts. A trial increase to
two million heartbeats caused large dependent-type expansion (about 23 GiB
combined process RSS), so it was stopped and removed. This is a failed route,
not a passing baseline or a universal resource bound.

The retained repair uses the existing `PullbackCertificate` and a small
constructed `SymmetricMassTransport.TransportCertificate` packaging the
already proved equality-transport results. It retains heterogeneous mass
equality, nonvanishing, radical equivalence, dimension and character.
A generic radical-membership lemma follows from the proved pullback-form
equality. These certificates are constructed in Lean, not new external
inputs or theorem assumptions.

The UV consumer retains its named action and certificate projection.
`StandardSMUVMass.mass_form_eq` proves equality with the original branching
pullback form. Coordinate and Yukawa consumers use the proved interfaces.
At the initial checkpoint, ScalarBlock remained at the conversion stop; the
later projection bridge closes that consumer. The membership proof retains its inferred proposition to keep
its exact implicit action data; `mass H` is that certificate's mass.
The resulting `defProp` style warning is recorded, not suppressed.
The continuous and UV model targets passed in 3.3 s and 3.8 s respectively.
No increased kernel checking budget or recursion limit is retained in the
formal source; the failed ScalarBlock trial is documented separately.

## Rejected Dependency Candidates

Retaining old TauCeti `b9e2e182804073eb92718b68a9baf37df8e189bd` failed on
the stable release, including deprecated APIs under its warning-as-error
policy. No policy was relaxed. The selected TauCeti revision passed initial
focused checks on Physlib's Mathlib release pin, but its full closure needed
`RootPairing.Base.exists_cartanMatrix_diagonal_mul_posDef`, absent there.
The shared Mathlib was therefore aligned to TauCeti's same-toolchain pin.
Upstream v4.36.0-rc1 was not selected. Interrupted/failed builds are diagnostics,
never successful project baselines.

## Initial Verification Checkpoint

- Focused aligned root-system, local-log and Physlib audit build: passed
  (3686 jobs), including 12 strict Physlib checks.
- E6 compact-chart, identity-component audits and Lie-group target: passed
  (3982 jobs).
- Certified mass consumers, coordinate/Yukawa connections, fundamental-group
  ports and Physlib audit: passed (4668 jobs). Additional strict checks:
  7 UV mass transports and 10 continuous mass transports.
- `python3 -m unittest discover -s tools/e6 -p 'test_*.py'`: 10 passed.
- `python3 tools/qque/audit_one_generation.py`: 4 passed.
- `python3 tools/delta-b-two/conventional-probes.py`: inverse regression and
  all 225 Grassmann monomial controls passed. Python is never a Lean premise.
- BNV bounded-support audit after abstract nonzero transport: passed
  (3359 jobs), including 173 strict transitive checks. Four-family foundations
  also pass their 131 strict checks.
- Full project verification: failed; the final stopped-state failure inventory
  is recorded below.
- Parent integration and merged-state verification were not performed because
  the full-project gate failed. The optional doc-gen4 executable and HTML site were not built.

Residual module-system recommendations and other compiler/linter warnings
are recorded at the final checkpoint; no blanket module migration or warning
suppression is part of this connection. Full external Physlib and HTML
site generation are outside the verification claim.

## Initial Integration Checklist

- Candidate pins and checked assumptions reviewed; acceptance is blocked by
  the full-project gate.
- Final sources reconciled in RELATED_LITERATURE.md: Physlib and the three
  derivative/IBP survey references are registered with their roles and limits.
- Child checkpoint records the unmerged stop. No parent/master integration
  or branch deletion is performed.

## Bounded ScalarBlock Conversion Check

The remaining concrete `StandardScalarBlock.embedding_mem_radical` statement
hits the default kernel budget even after using the proved mass-form
identity directly. A final bounded check retains that same statement and
proof with a local `maxHeartbeats = 800000`, RSS guard 16 GiB and wall guard
9 minutes. No recursion-limit or axiom-policy change is permitted. This is
one explicitly bounded conversion check, not a blanket increase for mass
transports. Result: kernel timeout after 347.9 seconds, peak process RSS 12917952 KiB;
operational guards did not trigger. The trial was removed from formal source.
This failed gate prevented integration at that checkpoint; see
[the stop record](conversion-stop.md). The later projection bridge supersedes it.

## Initial Stopped-State Inventory

The initial root `LEAN_NUM_THREADS=4 lake build` exposed three independent
compatibility failures:

1. `GUT.SU6.Adapters.StandardScalarBlock`: the original radical-membership
   rewrite does not match the transported certificate presentation. The bounded
   alternative above also failed kernel checking.
2. `Physics.StandardModel.Operators.SMGenerationSupport.quark_eighteen`:
   elaboration reaches the default recursion limit. A compact injectivity
   composition also failed; the original source was restored. No recursion
   limit increase is retained.
3. `Math`: simultaneous imports encounter duplicate declaration
   `SymmetricAlgebra.map_id`, defined by both
   `TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality` and
   `PhyslibAlpha.Mathematics.SymmetricAlgebra`. Individual Physlib audit success
   does not establish compatibility with the aggregate import closure.

Consequently no whole Math, Physics or GUT aggregate was certified on these
candidate pins. The individual passing targets above retain their narrower
meaning. No external dependency source was patched and no audit/import was
removed to bypass these failures. Optional doc-gen4 execution is deferred;
its synchronized candidate configuration alone is not a generator build.
The candidate branch was retained unmerged at that checkpoint. The subsequent
repair resolves the duplicate declaration; the carrier/projection pilot closes
the consumer conversion boundaries. Their narrower individual evidence is
separate from the full-project acceptance gate.


## Authorized Compatibility Repair Scope

The user authorized workarounds for the recorded failures. This follow-up keeps
all existing theorem statements and hypotheses, strict axiom policies and
v4.35.0 dependency pins. Its endpoint is a passing aggregate build with the
narrow algebra connection; derivative/IBP foundations remain outside scope.
Use abstract injective-composition and mass-radical interfaces to avoid concrete
conversion. For the name collision, test a separately named, attributed local
fragment of the pinned symmetric-algebra derivation source; retain the actual
Physlib exterior dependency and audit both sides together with TauCeti.
No installed dependency is modified. Stop if this needs new mathematical
premises, a substantial external fork or another resource-cap escalation.

The initial [compatibility repair](compatibility-repair.md) and subsequent
[carrier/projection pilot](carrier-pilot.md) record their implementation and
verification. The earlier failed runs above retain their original evidence level.

## Verified Compatibility And Integration

The final carrier/projection repair closes ScalarBlock, the Q18 coefficient,
the lower-generation local consumer and the downstream Q18 restricted/local
kernel. Focused strict audits pass (4910 jobs); the full
`LEAN_NUM_THREADS=4 lake build` passes (7569 jobs), including Math, Physics and
GUT and their persistent audits. No increased recursion/kernel limit, new
axiom, audit exemption or dependency edit is used by this repair.
The earlier failed gates remain diagnostic records, not the current baseline.

Root/docbuild toolchains and shared manifest revisions match. Installed
Mathlib, TauCeti and Physlib revisions match the root manifest and their source
trees are clean. The optional doc-gen4 executable and HTML site were not built.
Module-system recommendations, deprecated APIs and existing linter warnings
remain; no warning policy is relaxed.

The bibliography was reconciled in RELATED_LITERATURE.md: the selected Physlib
algebra sources and three derivative/IBP survey references retain their final
roles and limitations. The full-project pass certifies this combined closure,
not the larger external jet/analytic packages or derivative/IBP completeness.
See [final verification](verification.md) for commands and structural checks.

The verified child `audit/derivative-ibp-physlib-435` was merged with
`--no-ff` into `proof/derivative-ibp` under the recorded parent exception.
The parent had not advanced during the child work; there were no merge
conflicts. Merged-state `LEAN_NUM_THREADS=4 lake build` passes (7569 jobs)
and layout coverage passes (2081 modules). Final documentation checks are
recorded in the verification file. The parent remains unmerged into master;
no remote push was performed. Derivative/IBP proof work retains its separate
statement/assumption freeze.
