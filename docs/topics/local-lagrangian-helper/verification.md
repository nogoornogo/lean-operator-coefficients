# Verification

## Contract And Compatibility

The [contract](plan.md) was recorded before implementation on the recorded
topic branch. Published direct equations, coefficient interfaces and
nonderivative sources are unchanged. New sources are registered additively
in the Math and Physics aggregates. Dependency pins, root README and existing
audit allowances are unchanged.

Two new persistent audits inspect every declaration in the helper/consumer
namespaces, including constructors, instances and generated helpers. Math
rejects Physics/GUT imports; Physics rejects GUT imports. Both traverse axiom
dependencies and permit only `propext`, `Classical.choice` and `Quot.sound`.

## Focused Checks

```sh
LEAN_NUM_THREADS=2 lake build Math.Algebra.Audit.AuditLagrangianHelper Physics.FieldTheory.Jets.Audit.AuditLagrangianHelper Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter
```

The final focused gate passes 3313 jobs. New Math/Physics inventories check
393/22 declarations, including generated helpers; unchanged legacy adapter
inventories check 125/32. All 572 strict transitive checks pass. New sources
produce no warnings. Inherited dependency/module-system recommendations remain.
The scalar substitution bridge, all usage controls and actual Lorentz source
are included. No raised Lean limit, new axiom or import allowance is used.

## Full Build

```sh
LEAN_NUM_THREADS=2 lake build
```

The serialized full build passes 7691 jobs under the same address-space and
default-Lean limits. New source warnings are absent; inherited warnings and
dependency/module-system recommendations remain. Subsequent documentation-only
edits do not create another Lean baseline.

## Repository Gates

Layout passes 2197 modules. Navigation passes 157 indexed topics; the verified
unmerged stop is recorded in the outcome guide. Portable metadata passes 1178
documents/evidence files. Local links pass 1186 Markdown files, 7520 local
inline links and 127 heading fragments with zero errors. Diff checks pass.

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Checks use the existing 16 GiB address-space guard, default Lean elaboration
limits and a wall-clock timeout (180 seconds for the final focused command,
540 seconds for the full build). An intermediate four-thread invocation exited
with a runtime thread-creation error rather than a Lean diagnostic. Subsequent
checks use two threads, below the original four-thread cap; no memory, timeout,
heartbeat or recursion limit was increased to make a proof pass.

## Scope Review

Factories compile without caller-supplied equations or first-variation proofs.
Generic residual stability is still supplied; the actual scalar example
packages that proof for the existing Lorentz action. Mixed left signs are
compared with actual Grassmann contractions. The scalar comparison includes
the existing actual evolutionary derivation/substitution. The general mixed
result is a syntax-directed algebraic variation identity, not a new analytic
or arbitrary nonlinear substitution theorem.

Generated mixed equations are a two-sided differential closure. IBP is a linear
range; no homogeneous shell decomposition is assumed. No analytic action,
nonpolynomial truncation, symmetry discovery, quantum equivalence or universal
performance claim is part of the result. The source register and shared
bibliography contain the final result links and limited literature role.
Only the aggregate import files change among pre-existing Lean sources;
all implementations and audits are additive. The final diff/assumption review
agrees with the frozen contract and compiled examples. The verified endpoint
is retained on its topic branch, without a master merge or remote update.
