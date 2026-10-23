# Verification And Compatibility Evidence

Working branch: `proof/derivative-interface-adapters`; target: `master`.
The initial master worktree was clean. The user authorized the new topic and
implementation; no merge or push is included. The contract was recorded
before source implementation. All routes close using the existing APIs and
direct linear-map/subtype constructions, without an independent foundation.

## Proof Gates

All heavy checks use four Lean threads, a 540-second timeout and inherited
16 GiB per-process address-space guard. Default heartbeat, recursion and
kernel limits, dependency pins and audit allowlists remain unchanged.

```sh
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.JetAdapterControls Physics.FieldTheory.Jets.ScalarInputAdapter
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter Math.RepresentationTheory.Audit.AuditRelationCompleteness Math.RepresentationTheory.Audit.AuditFiniteLocalStatistics Math.RepresentationTheory.Audit.AuditMultiplicityCoordinates
LEAN_NUM_THREADS=4 lake build
```

Final consumer build passes 3293 jobs. Focused gate passes 3445 jobs:
68 new Math and 15 new Physics declarations, plus existing relation/local
statistics/multiplicity audits with 24, 16 and 31 checks. Total: 154 strict
transitive checks. Persistent public inventories include every new definition,
abbreviation and theorem, including inline simp declarations. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Math rejects Physics/GUT
imports and Physics rejects GUT imports.

The full build passes 7676 jobs, including all previously registered consumers.
Existing warnings and dependency module-system import recommendations remain.
No new-source linter warning, `sorry`, custom axiom or resource override is used.

## Published Interface Compatibility

```sh
git diff --name-only --diff-filter=M master -- '*.lean'
git diff master -- lean-toolchain lakefile.lean lake-manifest.json README.md
```

Only `Math.lean` and `Physics.lean` appear in the first command, with appended
new imports. The second command has no diff. All five implementation modules
and two audits are additive. Existing derivative-free declaration files,
signatures, imports and caller proof obligations are unchanged.

`legacyInputEquiv` and `mixedLegacyInput` are reflexive equivalences;
`mixed_legacy_map` proves equality with the existing positive-grade descent.
`zero_evaluation` proves coefficient compatibility with the existing original
exterior/symmetric source. Finite-local `emptyEquiv` recovers the original
coefficient input. The complete mixed control uses the actual computed IBP
relation in both direct and finite-local coordinates. The scalar consumer
uses the actual Lorentz action and proves the cross-grade seed constraint.

## Repository Gates And Stop

- Layout: 2182 modules, layers/imports/cycles/aggregate coverage passed.
- Topic index: 156 indexed topics with outcomes; no exception.
- Portable metadata: 1169 files passed.
- Local links: 1177 Markdown files, 7477 links and 125 heading fragments; zero errors.
- `git diff --check`: passed.

The bibliography, source roles, assumptions, interface map, input recipe and
result record agree. Documentation was reconciled after the final successful
Lean build; subsequent documentation-only edits required no additional Lean
build. All contracted obligations close. The verified topic remains unmerged.

## Uniform Entry Follow-Up

The [follow-up contract](uniform-entry-plan.md) was frozen before implementation.
`MixedOperatorInput` adds one source/coefficient equivalence indexed by every
natural-number derivative degree, including zero. Its source bridge at zero
is proved equivariant even with arbitrary direction actions. Positive inputs
and maps recover the old definitions. All earlier interfaces are retained.

```sh
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.MixedOperatorInput
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter Math.RepresentationTheory.Audit.AuditRelationCompleteness Math.RepresentationTheory.Audit.AuditFiniteLocalStatistics Math.RepresentationTheory.Audit.AuditMultiplicityCoordinates
LEAN_NUM_THREADS=4 lake build
```

Under the original resource gates, the module build passes 3266 jobs. Focused
checks pass 3446 jobs: 88 Math and 15 Physics adapter declarations, including
all 20 new uniform-entry declarations, plus the unchanged 24/16/31 legacy
checks (174 checks total). The full build passes 7677 jobs. No new source
warning, axiom, audit allowance or dependency change is introduced.

Layout passes 2183 modules; navigation passes 156 topics with outcomes;
portable metadata passes 1170 files. Final local-link verification passes
1178 Markdown files, 7480 links and 125 fragments; `git diff --check` passes. No Lean build is rerun for
those subsequent documentation-only edits. Published nonderivative sources
remain unchanged. This completed follow-up is committed on the same topic
branch and remains unmerged.

## Purpose-Specific Operation And Selection Follow-Up

The [contract](purpose-specific-plan.md) was recorded before implementation.
The shared operation record is optional and preserves all prior factories.
Graded and full-EOM factories retain their original data/certificate inputs;
actual mixed and Lorentz scalar usage compile with the same dot-operations.
Invariant source selection pulls back the complete relation module and has
a proved linear equivalence to its actual image in the full quotient.
Restriction is proved; extension of arbitrary invariant coefficients is not
assumed. The scalar wave/cubic selection retains its actual EOM coefficient law.

```sh
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.DerivativeInterfaceControls Physics.FieldTheory.Jets.ScalarDerivativeInterface
LEAN_NUM_THREADS=4 lake build Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter Math.RepresentationTheory.Audit.AuditRelationCompleteness Math.RepresentationTheory.Audit.AuditFiniteLocalStatistics Math.RepresentationTheory.Audit.AuditMultiplicityCoordinates
LEAN_NUM_THREADS=4 lake build
```

With the original resource/default-Lean gates, the consumer build passes
3297 jobs, the focused gate 3449 jobs and the full build 7680 jobs. Adapter
inventories now contain 125 Math and 32 Physics checks, including 37 new Math
and 17 new Physics entries (the input type, constructor and field projections
are included). Together with the unchanged 24/16/31 old checks, the focused
gate reports 228 strict transitive checks. A first control elaboration hit the
default heartbeat bound; explicit source parameters and local reducible module
instances resolved it without increasing any Lean limit or changing a theorem.
No new-source warning or new axiom/import allowance remains.

Compatibility comparison against master still reports modifications only to
`Math.lean` and `Physics.lean` among pre-existing Lean files. These append new
imports; all implementation changes are additive. Published nonderivative
interfaces, existing caller proofs, dependency pins and root README are intact.

Layout passes 2186 modules; topic navigation passes 156 topics with outcomes;
portable metadata passes 1171 files. Final local links pass 1179 Markdown
files, 7487 links and 125 heading fragments; `git diff --check` passes. Subsequent documentation-only edits do not
require a further Lean build. The bibliography, source roles, assumptions and
input recipe agree. The verified topic remains unmerged.

## Master Integration

The user explicitly authorized integration of the completed topic into master.
The starting topic worktree was clean and master was its ancestor with no
independent target changes. `git merge --no-ff proof/derivative-interface-adapters`
completed without conflicts. The merged tree equals the verified topic tree;
no source or assumption was changed for integration.

The same focused command above was rerun on master: 3449 jobs passed, with
125 Math and 32 Physics adapter checks and 24/16/31 unchanged legacy checks
(228 strict transitive checks total). The serialized full `lake build` passed
7680 jobs under the original four-thread, timeout, memory and default-Lean gates.
Existing warnings and dependency module-system recommendations remain.

Compatibility comparison against the first merge parent confirms that only
Math/Physics aggregate imports changed among pre-existing Lean files. All
implementation modules are additive; published nonderivative sources/signatures,
root README, dependencies and audit allowances remain unchanged. The bibliography
and source register already contain final result links and inherited scope;
no additional external source or completeness premise is imported.

Final repository gates pass: 2186 layout modules; 1179 Markdown files with
7490 local links and 127 heading fragments; 156 topics with outcomes; 1171
portable metadata files; `git diff --check`. These documentation-only updates
do not create another Lean proof baseline. Earlier unmerged-stop text
in the phase records above describes those checkpoints, superseded by this
integration. General Lagrangian input, nonlinear fermionic EOM, independent
on-shell grading and extension of every selected invariant coefficient remain
outside the result.

The local topic branch is retired after confirming its HEAD is reachable from
master and no worktree uses it. Historical branch names are retained. No remote
push/deletion or unrelated branch/worktree cleanup is included.
