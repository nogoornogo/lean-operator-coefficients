# Structural support verification

Continuation after `checkpoint 01`, on `proof/sm-computable-characters`; no merge or
push authorized. See [results](structural-results.md) for the distinction between
proved adapters and the still-open complete support consumer.

Focused checks:

    lake build TauCeti.LinearAlgebra.Multilinear.Polarization
    lake build Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport
    node tools/layout/check-layout.mjs
    git diff --check

The pinned polarization dependency built successfully. The final focused audit
build passed (4314 jobs): 34 Math and 21 Physics strict transitive standard-axiom
checks, together with the layer checks. Layout passed for 1685 modules, including
aggregate coverage, local imports, cycles and relocation checks. No forbidden
proof token was found in the new proof files. The diff check passed.

Early elaboration failures involved inferred representation aliases, tensor
additive-instance diamonds, transport through a complementary-degree equality,
and nested coercions. Explicit types and pointwise proofs resolved them.
The first kernel-zero transport exceeded default elaboration heartbeats;
using the existing coefficient-equivalence certificate directly resolved it.
The first Q6 component-injectivity proof hit default recursion depth; applying
the two proved injections pointwise resolved it. No Lean resource option was
raised, and no failed or partial theorem is retained.

The first full build did not finish. On stage 01 at approximately 16:46 JST,
the kernel reported global OOM with no free swap and killed VS Code renderer
processes; the extension host then terminated. The build log ended at
7033/7053, without a final result. The source edits and earlier focused checks
were retained; no full-build success is inferred from the interrupted run.
No numerical coefficient recurrence is executed by the new structural proofs.
Both CSVs, the root README, dependency pins and Weyl premise are unchanged.

## Post-interruption implementation review

The [plan revision](structural-plan.md#revision-after-the-interrupted-build)
restores `SymmetricMultilinearProjection.lean` byte-for-byte to the preceding
commit and puts the new lemma in `SymmetricMultilinearDiagonal.lean`. The
capacity proof now imports the structural kernel interfaces directly, uses
actual field-basis cardinality, and no longer imports the numerical rank
classifier or LLHH arithmetic result. Local irreducibility annotations keep
the Cauchy consumers on their proved interfaces. Both structural audits now
reject imports of the sparse/grouped numerical evaluators; the Physics audit
also rejects the numerical rank modules and closed neutral certificates.

The guarded runner now supports a smaller RSS stopping budget and a host
`MemAvailable` reserve and cached-certificate preconditions. Its eight small
process controls pass. It remains a
sampling monitor, not a hard memory limit or theorem premise.

A first monitored rebuild without limiting the Lean task pool stopped at
21.1 s with sampled group RSS 9026648 KiB. A second dependency rebuild stopped
at 2.8 s with 9241564 KiB. Both crossed the requested 6 GiB stopping threshold
before the polling loop could interrupt them; neither is reported as a
successful proof check. Independent Lake jobs can import the same large
library environment concurrently even when no character DP is evaluated.
The single-target commands below therefore also set `LEAN_NUM_THREADS=1`;
no second Lean command runs beside them.

    LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport /tmp/sm-structural-math-final.log
    LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport /tmp/sm-structural-physics-final.log
    python3 tools/exact-rank/test-kernel-probe.py

The revised Math audit passed (4008 jobs, 34 strict transitive checks plus
layer and numerical-import checks), in 14.8 s with sampled group peak
5174052 KiB, about 4.94 GiB. The isolated SU2 symmetric-support dependency
rebuild also passed, in 27.6 s with 4785360 KiB. These are observed run
measurements, not uniform complexity bounds.

The serialized Physics dependency rebuild reached the 300 s wall-clock
stopping condition, with sampled peak 4996676 KiB (about 4.77 GiB). By then
the three revised Physics proof modules had built successfully, including
`SMGenerationSupport` in 2.7 s. The remaining audit then passed on rerun
(4190 jobs, 23 strict transitive checks plus layer/numerical-import checks),
in 4.5 s with sampled peak 5262140 KiB (about 5.02 GiB). No Lean resource
option was raised. Together the revised audits cover 57 endpoints.

Two bounded negative controls prepend an evaluator import to a temporary
copy of each audit and run it with ordinary `lake env lean`. The Math
control failed as expected with `imports numerical evaluator
Math.RepresentationTheory.ComputableWeightPolynomial`; the Physics control
failed with `imports numerical evaluator/certificate
Physics.StandardModel.Operators.LLHHKernelRank`. Thus the new guard is
exercised on actual imported environments, in addition to passing on the
intended structural roots. Their sampled peaks were 5089592 and 5327724 KiB.

The first full-project `LEAN_NUM_THREADS=1 lake --no-build build` preflight
returned 3, reporting 41 stale frontier targets. This neither elaborates
those targets nor verifies a full build. The Q18-only preflight also returned
3 because upstream symbolic/rank-interface caches were stale. Full-project
acceptance remains pending until those dependencies and the numerical
certificate cache boundary have been checked; no heavy closed Q18 recurrence
has been rerun in this review.

The unchanged symbolic backend dependencies were then rebuilt separately
through `SMGroupedCharacter` (4426 jobs, 105.2 s, sampled peak 5726224 KiB,
about 5.46 GiB). This target excludes the closed Q18/Q6 examples. A subsequent
Q18 no-build preflight reached the precise remaining frontier:
`SMNeutralCertificates.Q18Part0` and `SMCoefficientAssembly` are stale.
It returned 3 without rechecking the closed arithmetic.

The runner now supports repeated `--require-cached MODULE` preconditions.
The guarded full-project command in the [tool guide](../../../tools/exact-rank/README.md#guarded-structural-proof-checks)
was exercised: it refused launch after the Q18 preflight returned 3. No full
build or closed Q18 expansion ran behind this check. The eight controls also
verify stale-cache refusal and propagation of the actual build result after
a successful cache check. This preserves the old certificate sources and
normal full-build gate; it does not bypass or satisfy that gate. The full
project build remains **outstanding**. The structural adapter checkpoint has
focused verification only and is not completion of the full support theorem.

Layout passed for 1686 modules. Final documentation links passed for 861
Markdown files, 5313 local links and 109 fragments, zero errors (approved
read-only retry for the sandbox's `git ls-files` restriction). The diff check
passed. The retained proof sources contain
no `sorry`, custom axiom, `native_decide` or `implemented_by`, and the shared
projection, both CSVs, root README, pins and numerical proof sources have no
diff against the preceding commit.

The user subsequently approved the [Q18 support replacement](q18-support-results.md).
Its [verification record](q18-support-verification.md) supersedes the Q18 cache
blocker above: the thirteen numerical modules are archived source text and
the new active Q18 proof is structural. Earlier run measurements above still
describe their own checkpoint.
