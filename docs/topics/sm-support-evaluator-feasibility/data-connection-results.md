# Revised SM data connection and bounded use

## Result

The [connection revision](data-connection-plan.md) is verified. Executable
metadata is connected to actual full joint SM support, Higgs support and
original coefficient spaces without new computational support proofs.
The earlier [resource-stop evidence](data-layer-results.md) remains unchanged;
the checked revision supersedes that implementation boundary.

The active interfaces are:

- [JointSourceReexpression](../../../Math/RepresentationTheory/JointSourceReexpression.lean):
  put an executable expression in the outer presentation field while retaining
  its actual representation equivalence by ordinary equality transport.
- [SMCoreSourceData](../../../Physics/StandardModel/Operators/SMCoreSourceData.lean):
  executable ten-species `coreData`, with `corePresentation` using that exact
  expression before the dependent equivalence dispatch. Every mathematical
  core, conjugate, complementary degree and overflow is covered.
- [SMJointSupportData](../../../Physics/StandardModel/Operators/SMJointSupportData.lean):
  executable content/Higgs metadata, compact occupation indices,
  `dataSupport_iff`, `higgsDataSupport_iff`, and `original_ql_iff`.
- [Ordinary consumers](../../../Physics/StandardModel/Operators/SMJointSupportDataExamples.lean):
  generic component/original-space transport, actual mixed d,u,Q,L allowance,
  Q18 with h=0,d=6 allowance, and Q/conjugate-Q prohibition for all Higgs degrees.
  Closed positive witnesses choose the source/Higgs input explicitly and use
  existing algebraic family lemmas; they do not search occupations/components.

The original input dictionary, all-degree quantifiers, statistics, independent
left/right actions and scalar cyclic q/l equations are preserved. No Weyl
multiplicity law, numerical table, supplied occurrence premise or new axiom
is introduced. New proofs use ordinary constructor, equality and algebraic
lemmas; there is no `decide` variant, `native_decide`, `omega`, `norm_num` or
Boolean-reflection support proof. Existing mathematical/family proofs remain
unchanged. The old intermediate `coreData_eq` projection equality is not a new
required API; the final support equivalence is proved through actual sources.

## What changed at the expensive connection

Import loading alone passed in 4.0 s at 5037924 KiB. Progress files localized
the costly old comparison to `coreData_eq`; comparison of the first species
alone also failed to finish within the old resource budget. This is not a
large-content search and is not evidence of optimizer miscompilation.

Two properties of the revision keep that comparison out of the consumer path:

1. The mathematical syntax equality is used *before* representation transport.
   `corePresentation.expression` is explicitly `coreData`, rather than a
   projection through a dependent Fin dispatch carrying large equivalences.
2. Data support is reindexed to the new joint presentation. The existing
   `JointContentPresentation.allowed_iff` is applied twice to the **same actual
   full joint source**, once for each presentation. The old presentation stays
   abstract. No independent color/spin choices replace a joint branch.

Concrete reducible tensor-product additive instances, already used by the
existing SM presentation modules, also matter for elaboration. A reexpress-first
Q adapter without the concrete local instances hit the unchanged
200000-heartbeat `isDefEq` limit in 18.8 s (5183392 KiB); adding the existing
local instance pattern made that adapter pass in 3.5 s (5053252 KiB).
This controlled comparison supports the elaboration fix, but does not isolate
every allocation in the old interrupted comparison.

## Failure and cancellation accounting

The resumed initial untyped localization hit the RSS guard at 54.6 s,
10501780 KiB. A direct natural-number case comparison hit it at 60.7 s,
10492008 KiB; a direct first-species comparison hit it at 62.1 s,
10489052 KiB. Slight sampled overshoot is retained in the record. No higher
memory or proof limit was used. Other localization variants were deliberately
cancelled when their progress established the same costly boundary or before
changing instrumentation; no successful timing/peak is assigned to those
cancelled runs. An explicit normalization attempt and generic-instance-only
variant were not counted as proofs. No failed file is accepted by an audit.

The earlier stderr marker was not visible during an interrupted check in this
environment, so the retained reproducer uses explicit `/tmp` progress files.
[connection-probe.py](../../../tools/structural-support/connection-probe.py)
can regenerate the old projection diagnostic or the imports-only control;
it is not the production connection and is not rerun automatically.

## Acceptance and scope of the resource statement

The revised focused connection and fresh downstream consumer checks use a
120-second guard, 10 GiB sampled process-group RSS, 4 GiB host reserve and one
Lean thread, with pins and proof options unchanged. All accepted revised
checks finish below those guards; exact measurements are retained in the
[machine-readable verification](../../../tools/structural-support/results/data-connection-summary.json).

Fresh importing consumer files check an arbitrary-pattern transport theorem,
a mixed four-fermion allowance, the actual Q18 data-support witness, the mixed
negative, and Q18 component transport with a supplied joint certificate.
These are newly elaborated applications, not just `#check` on cached results.
Generic arguments stay abstract and old representation decompositions need
not be expanded when using the interface. Runtime metadata construction is
also checked with a runtime degree input and balanced Q18 occupations
(8000 branches); printed counts are diagnostics, not support proofs.

There is also a structural bound on what the data builder traverses: the SM
composition has ten species and three generation slots per species, each using
a finite core-degree template, plus one Higgs atom. Sums/tensors remain syntax;
the builder does not distribute them into the branch Cartesian product or
enumerate contents. Thus increasing an input degree does not start an unbounded
occupation/component search inside this connection. This observation concerns
metadata construction, not arbitrary proofs of the support predicate.

This gives a measured bound for the retained connection and named consumers.
It is **not** a universal running-time/RAM theorem for every possible input,
proof term, arbitrary unfolding or witness search. In particular, transporting
a supplied component witness is distinct from finding or proving one. The old
noncomputable general decision functions and exhaustive color search are not
made executable or assigned a new performance guarantee by this change.

## Verified checkpoint

| Accepted check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Generic reexpression helper build | 5.0 | 4892440 |
| Ten-species core presentation build | 5.5 | 5143284 |
| Full support/Higgs/original-space bridge build | 6.0 | 5142728 |
| Ordinary mixed/Q18/negative consumers build | 5.5 | 5137528 |
| Math/Physics persistent audit builds | 7.8 | 5463064 |
| Fresh importing applications + five strict checks | 3.8 | 5040200 |
| Runtime degree 6 metadata | 3.8 | 5048212 |
| Runtime degree 13 overflow metadata | 3.5 | 5036556 |
| Direct Physics audit: 34 strict checks | 3.5 | 5390636 |
| Direct Math audit: two strict checks | 3.8 | 5171520 |
| Full default-root `lake build GUT` | 16.0 | 6694332 |

The focused bridge is about 4.90 GiB, fresh importing applications about
4.81 GiB; the full-library sampled peak is about 6.38 GiB. The full build
passes all 7335 jobs with zero warnings/errors. Imports were cached for
focused checks; the new modules were built before the fresh application files.
These are successful complete runs, not merely prefixes below the guard.

Layout passes for 1949 modules. Local links pass for 980 Markdown files,
5993 links and 113 fragments, zero errors; the unchanged read-only checker
uses its sandbox-subprocess retry where needed. Diff/source-policy checks
pass. The two persistent audits were rerun directly in addition to the full
build, and all new public interfaces are registered in Math/Physics aggregates.
No axiom allowlist, pin, proof limit, original support definition or old
classification table changed. No merge, push or branch deletion was performed.
