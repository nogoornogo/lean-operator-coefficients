# Verification

The predecessor verification portfolio is closed on its recorded branch.
This bounded child owns the evidence below and is integrated into its
recorded parent, `proof/derivative-literature-foundations`.

## Proof gates

All Lean acceptance runs used two compiler threads, CPU affinity to cores
0,1, a 16 GiB address-space guard per process, default heartbeat/kernel limits
and the frozen 180-second focused / 540-second full ceilings. The temporary
wrapper used for these commands sets `resource.RLIMIT_AS` to 16*1024^3 for
both soft and hard limits, then calls `os.execvp` with its command arguments.
It is build machinery, not a proof premise or source-controlled artifact.

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.RepresentationTheory.Audit.AuditScalarTwoSpeciesCompleteness \
  Math.Algebra.Audit.AuditScalarCompletenessHelpers \
  Physics.FieldTheory.Jets.Audit.AuditScalarCompleteness
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
```

The combined focused audit build passes, 3323 jobs; after the final grade and
fixed-image proofs, the focused Physics audit also passes, 3315 jobs.
The serialized full build passes,
7749 jobs. The full invocation reports about nine seconds with the focused
dependencies already built; this is not a clean-cache build estimate. No
acceptance guard expires. A monolithic contraction simplification hit the
default heartbeat limit during development; splitting the differentiated
summand into its own lemma resolves it without changing limits.

The persistent audits inventory entire namespaces, including definitions,
generated support declarations and instances. Every collected transitive
axiom must be one of propext, Classical.choice and Quot.sound. Math import
audits exclude Physics/GUT; Physics import audits exclude GUT.

| Namespace | Strict declaration checks |
| --- | ---: |
| Math.ScalarFirstJetReduction | 37 |
| Math.ScalarTwoSpeciesCompleteness | 122 |
| Math.ScalarDegreeTwo | 17 |
| Math.FourWaveEvaluation | 28 |
| GUT.LorentzFiniteControls | 37 |
| GUT.ScalarQuarticTwoCompleteness | 35 |
| GUT.ScalarQuarticFourWitness | 19 |
| GUT.ScalarQuarticContractions | 32 |
| Total | 327 |

No sorry, custom axiom, audit exception, extra theorem hypothesis or dependency
change is introduced. The remaining warnings are module-system advisories
from existing-style direct mathlib imports, including the new pderiv, finite
coefficient and linear-extension imports. No tactic/linter warning remains
in the accepted new proofs. No module-system migration is attempted.

## Exact diagnostic gates

```sh
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
python3 tools/derivative-literature/check-scalar-group.py
```

All three pass using the Python standard library and exact rational
arithmetic. C1 gives (1,1,0)/(1,1,1) in the specified contents. The C2
infinitesimal and actual finite-group diagnostics both give (1,0,1), with
source sizes 1,20,305. The actual-group calculation verifies the normalized
finite dual, all relation/group rows and the literal invariant witness
vectors; its order-four dual has 48 nonzero entries. None is a Lean premise.
The new script's fixed matrices are separately proved actual Lorentz
direction matrices, but its polynomial-coordinate transport and arbitrary
group invariance are not thereby formalized.

The primary PDF text was reinspected at the pinned C1/C2 equations and
representatives listed in [references](references.md). Screenshot retrieval
returned cache misses; visual page inspection is not claimed. No extra
literature theorem is assumed.

## Repository gates and review

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Layout passes for 2254 modules, including layer rules, cycles, aggregate
coverage and relocation audits. Navigation passes for 162 topics and 162
outcomes without pending exceptions; metadata passes for 1227 portable files.
The link checker passes for 1235 Markdown files, 7905 local inline links and
153 heading fragments, with zero errors. Whitespace checking passes.
Dependency pins, original public input records
and the root README remain unchanged. The diff/assumption review distinguishes
actual source reconstruction, full differential EOM closure, linear IBP,
ordinary versus invariant extension, actual group upper bounds and the
noninvariant four-wave dual. The [results](results.md) retain the exact
unproved C2 order-four and paper-convention obligations.

## Additional validation gate

The [additional contract](validation-plan.md) and [results](validation.md)
cover the existing/new input and literature verification. The new Math and
Physics consumer namespaces contain 18 and 31 strictly audited declarations,
respectively. The original 327 topic declarations are rechecked as well;
the combined topic namespace inventory is 376, with no extra allowed axiom.

The focused build passes, 3324 jobs:

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.RepresentationTheory.Audit.AuditScalarCompletenessChecks \
  Physics.FieldTheory.Jets.Audit.AuditScalarCompletenessChecks
```

All fourteen audit source files below were then separately re-elaborated
with `lake env lean -j2`, under the same affinity, address-space and per-file
180-second guards. This re-executes their strict inventories rather than
only reading cached build messages.

| Layer | Audit paths relative to the repository |
| --- | --- |
| Math | Math/RepresentationTheory/Audit/AuditDerivativeLiterature.lean |
| Math | Math/RepresentationTheory/Audit/AuditDerivativeLiteratureFoundations.lean |
| Math | Math/RepresentationTheory/Audit/AuditNonDerivativeInputChecks.lean |
| Math | Math/RepresentationTheory/Audit/AuditExtendedDerivativeChecks.lean |
| Math | Math/RepresentationTheory/Audit/AuditScalarTwoSpeciesCompleteness.lean |
| Math | Math/Algebra/Audit/AuditScalarCompletenessHelpers.lean |
| Math | Math/RepresentationTheory/Audit/AuditScalarCompletenessChecks.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditDerivativeLiterature.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditLiteratureFoundations.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditLiteratureRecheck.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditNonDerivativeModelChecks.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditExtendedDerivativeChecks.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditScalarCompleteness.lean |
| Physics | Physics/FieldTheory/Jets/Audit/AuditScalarCompletenessChecks.lean |

Existing derivative/nonderivative, mixed-statistics, helper/generated input,
presentation and reality consumers pass at their stated scopes. The original
six-case consumer audit passes each C1–C6 namespace. No old proof scope or
conditional input is promoted by this regression.

The serialized full build passes, 7753 jobs, under the original two-thread,
two-core, 16 GiB and 540-second guard. All proof acceptance runs finish inside
the guards with default heartbeat limits. The accepted new consumer files
have no tactic/linter warnings; existing mathlib module-system advisories
remain. No sorry, custom axiom, allowance or dependency change is introduced.

```sh
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
python3 tools/derivative-literature/check-scalar-group.py
python3 tools/derivative-literature/check-scalar-waves.py
```

All four exact diagnostics pass without changed expectations. The new direct
expansion imports no rank implementation: six configurations give 2520
divergence and 330 EOM-product checks, 144 permutations, 12 rescalings and
eight literal normalized polynomial comparisons. Assumption-removal controls
return divergence -48 and EOM-product 12; the group control returns 24/60.
These are supplementary finite checks, not proof premises.

Four primary-source cases reach their recorded local endpoint, including the
additional Cao density reading. Only primary PDF text is used; screenshot
retrieval returned cache misses. No image inspection, full-paper verification
or quantum result is asserted. References and the bibliography are reconciled.

Layout passes for 2258 modules, including aggregate/import coverage.
Navigation passes for 162 topics/outcomes without pending exceptions;
metadata passes for 1229 portable files. Local links pass for 1237 Markdown
files, 7929 links and 156 heading fragments, with zero errors. Whitespace
checking passes. The verified changes are committed on the existing child
branch without a parent/master merge or remote update. Public input definitions,
dependency pins and the root README remain unchanged. The C2 order-four
full invariant completeness and convention boundary remain unproved.

## Parent integration

The user accepted closure at this bounded scope. The child was merged with
`--no-ff` into its recorded non-master parent. The parent had not advanced
outside the child's ancestry. On the merged state, all fourteen listed
strict audit sources were re-elaborated successfully, the full build passed
7753 jobs, and all four exact diagnostics passed unchanged. Layout passed
2258 modules; navigation and portable metadata checks passed. Local links
and whitespace checks passed. References were reconciled with the maintained
bibliography before integration. The local child branch was deleted after
reachability and worktree checks. No master merge or remote update was made.

The full C2 order-four invariant coefficient theorem is explicitly reserved
for a separately authorized follow-up; it is not part of this closure.
