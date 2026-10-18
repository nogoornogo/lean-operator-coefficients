# Compact enumeration implementation checkpoint

Authorized by the user after `checkpoint 01`; see the
[implementation contract](implementation-plan.md). Branch remains
`audit/sm-support-evaluator-feasibility`, integration target master with no
merge/push authorization. Implementation and acceptance are complete following the explicitly authorized
10 GiB full-build check below. The original 6 GiB failure remains recorded;
no general compiled evaluator or rewrite decision is claimed.

## Implemented

`Math.CompactGenerationOccupations` retains the prototype's uniform sum and
attainability proofs and constructs an actual equivalence

```text
(Sigma a : Fin (n+1), Fin (n-a.val+1)) ≃ GenerationTensorSupport.Occupation n.
```

Its `fintype` transports the dependent triangular enumeration with no executed
deduplication. `choiceFintype` selects that enumeration explicitly at every
content-tree leaf. Neither replaces a default global instance.

`SMCompactSupportDecision.contentDecision` and `higgsDecision` return decisions
for the original structural predicates. All color/weak/two-spin branch choices
stay joint. Source construction, statistics and theorem premises are unchanged.
These opt-in definitions remain noncomputable for compiled execution; the first
endpoint is closed kernel checking, not an all-content compiled solver.

`SMCompactSupportExamples.q18Allowed` proves actual Q18 OriginalSpace allowance
at h=0,d=6; `mixedForbidden` proves original Q/conjugate-Q prohibition at h=d=0.
Both instantiate k=1,q=l=0, have neutral charges and use the original structural
iff with kernel decisions. The latter is a genuine semisimple support failure,
not rejection merely by a residual or hypercharge filter.

Math/Physics aggregates register all five new modules, including two persistent
strict audits. The [dossier](../../proof/current/applications/Physics/SM_COMPACT_SUPPORT_DECISION.md)
and Math/Physics assumptions record the actual inputs and verification scope.

## Development correction and limits

An initial compact-list-to-Finset implementation still executed deduplication.
Its monolithic cardinality/existence/Q18/negative gate was interrupted at
6326516 KiB after 10.8 s. The log did not isolate which goal was active, so this
is not evidence attributing that memory to one exact subexpression.

Within the same triangular enumeration route, the implementation was refined
to the dependent index and a proved equivalence, avoiding that deduplication.
Cardinality and model checks were then run separately. This changed the
representation/algorithm, not the resource ceiling. The original monolithic
attempt is not counted as passing.

A theorem-local `letI` with `decide +kernel` also exposed a kernel-helper
free-variable error. File-local explicit instance selection fixes it without
new axioms or proof-limit changes. Ordinary sum association/projection proof
errors and one linter warning were corrected; the final focused builds have
no warnings. No `sorry` or custom axiom was added.

## Verification measurements

All runs serialized with cached imports, one Lean thread, 300-second cap,
6 GiB sampled group RSS and 4 GiB host available-memory reserve. Sampled
memory is not a hard OS limit. No raised Lean options or numerical replay.

| check | exit | seconds | peak KiB | outcome |
| --- | --- | --- | --- | --- |
| final Math/Physics decision focused build | 0 | 7.3 | 5117784 | 4605 jobs, no warnings |
| compact occupation cardinality/existence | 0 | 3.0 | 4345316 | closed kernel count 190 and trivial existence at degree 18 |
| original Q18 and neutral mixed negative probe | 0 | 5.5 | 5331448 | both actual OriginalSpace results kernel-checked |
| final registered examples focused build | 0 | 11.3 | 5406672 | 4606 jobs; rebuilt final Math/Physics sources and examples |
| final strict audit build | 0 | 6.8 | 5480060 | 4655 jobs; 13 Math and 12 Physics checks, plus original structural audit |
| fresh wrong positive and negative candidates | 1 | 4.3 | 5311972 | both rejected specifically as false |
| initial full default-root `lake build GUT` | -2 | 5.1 | 6325176 | interrupted at 6 GiB; later authorized completion below |

Commands use the existing runner, for example:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build Physics.StandardModel.Operators.Audit.AuditSMCompactSupport /tmp/compact-audit.log --rss-limit-gib 6 --min-available-gib 4
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build GUT /tmp/compact-full-build.log --rss-limit-gib 6 --min-available-gib 4
```

GUT is the default root and imports Math and Physics. This full attempt replayed
existing Math structural audits (2018 checks) and the new Math audit before its
RSS stop. At checkpoint `checkpoint 02`, no completed full build or merged-state
result was asserted and no larger retry had been performed. Prior historical full-support verification
used 10 GiB and observed more than 6 GiB; that is context, not authorization to
silently change this implementation contract's ceiling.

The cardinality/existence and rejection sources are retained as diagnostic
text under `tools/structural-support/probes/compact-cardinality.lean.txt` and
`compact-rejections.lean.txt`. The latter intentionally fails. Successful Q18
and negative proofs are active registered sources, not only transient logs.
All new named declarations are listed in the persistent strict audits.

## Authorized full-build completion

After `checkpoint 02`, the user explicitly authorized 10 GiB for the full build only
and requested deferring any rewrite decision. The serialized command

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build GUT /tmp/compact-authorized-full.log --rss-limit-gib 10 --min-available-gib 4
```

passed **7325 jobs**, exit 0, **11.3 s**, sampled group peak **6721952 KiB**
(about 6.41 GiB), with no warnings/errors and no interruption. GUT is the
default root and imports Math and Physics. The individual closed-probe ceiling
remained 6 GiB; no Lean proof option, axiom boundary or dependency pin changed.
Only the outstanding full gate was repeated; successful probes were not replayed
unnecessarily. This completes the bounded compact implementation acceptance.

## Remaining scope and later design judgment

No full-content `#eval`, 107-row comparison, assignment enumeration, large
negative-search complexity result or fast color/CG refinement is claimed.
Review-requested unrelated documentation fixes remain deferred. No merge/push.
Repository checks pass: layout (1939 modules), retired certificates (19 hashes,
15 absent modules), local links (969 Markdown files, 5910 links, 111 fragments, zero errors) and
`git diff --check`. The layout check first
required the new import audit to include the existing original-module diagnostic;
that was fixed without relaxing its gate, then both new audits were rebuilt.
No checker or audit allowlist was changed.


[Later design judgment](design-review-boundary.md) distinguishes the completed
checks from the unknown compiled/exhaustive-search performance. The user has
not decided or authorized a rewrite; no further evaluator implementation or
107-row run was started. Completion does not authorize merge or push.


Final post-completion repository checks pass: layout 1939 modules, retired
certificate checks 19 hashes/15 absent modules, local links 970 Markdown files,
5910 links and 111 fragments with zero errors, and `git diff --check`.
The final acceptance-record edits are documentation only; no Lean build was
rerun after the successful authorized full build because no Lean source changed.
