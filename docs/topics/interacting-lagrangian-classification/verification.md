# Verification

## Acceptance And Scope

The frozen plan precedes the implementation. New sources add the actual
unbounded monomial basis, complete generated rows, inverse coordinate maps,
exact selected preimages, a closed all-degree polynomial family and literature
consumers. Existing APIs, dependency pins, proof limits and audit allowances
are unchanged. No `sorry` or custom axiom is used.

The mathematical audit covers all declarations in the new namespaces and the
extended expression namespace. The physical audit covers every source consumer.
Both collect transitive axioms and allow only `propext`, `Classical.choice`
and `Quot.sound`. Math rejects Physics/GUT imports; Physics rejects GUT imports.

## Commands And Current State

Focused gate: PASS, 3,961 jobs. The mathematical audit performs 314 strict
transitive checks and the physical source audit 37, for 351 checks in total.
The final serialized full build passes 8,016 jobs. New source warnings are
module-system import recommendations in four mathematical modules; there
are no unresolved theorem diagnostics. Inherited repository warnings remain.

Layout passes 2,519 modules. Navigation passes 166 indexed topics and 166
outcomes with no pending exception. Portable metadata passes 1,267 files.
Local links pass 1,275 Markdown files, 8,231 links and 156 heading fragments
with zero errors. The final diff whitespace check passes.

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditInteractingLagrangian Physics.FieldTheory.Jets.Audit.AuditInteractingLagrangian
LEAN_NUM_THREADS=2 lake build
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Build commands use a 16 GiB address-space cap and 540-second timeout guard.
Intermediate diagnostics included an explicit scalar Leibniz-order/coercion
correction and audit counter type annotations. These were repaired in source;
no heartbeat, recursion, kernel or resource limit was raised. Source module-system
recommendations are reported separately from theorem failures.

## Claims Review

The general equivalence is an exact potentially infinite linear presentation,
not an executable universal normal-form solver. Basis ordering and optional
selected bases are noncomputable choices. Full-group stability is explicit or
packaged by an existing model; no generic symmetry discovery is asserted.
The no-cutoff and cancelling-equation counterexamples retain their exact scope.
All literature and artificial cases remain linked from the
[validation report](literature-validation.md).


The first sandboxed link-check attempt hit `spawnSync git EPERM`. The unchanged
checker was rerun with Git subprocess permission and passed; no checker or
allowlist was weakened. Disposable build logs remain outside source control.


[Master integration verification](integration-verification.md) records the
merged-state checks for this topic and both completed successors.
