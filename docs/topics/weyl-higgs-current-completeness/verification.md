# C5 Verification

The [completed result](results.md) proves whole-grade coefficient
completeness. The earlier input/current stop is retained as an
[input checkpoint](input-checkpoint.md); its missing foundations are
superseded by the [resumed contract](completeness-plan.md).

## Proof checks and strict inventories

Each new source was built before its dependent consumer. Final focused
builds pass for whole-grade injectivity, wave-word moments, arbitrary
Lorentz/internal invariance, admitted wave coefficient, normalization,
coefficient equivalence and native literature consumers. The final native
consumer build passes 4028 jobs.

All six persistent inventories were freshly elaborated on the final source
state. Full namespace inventories include generated declarations and audit
their private dependencies transitively.

| Inventory | Transitive declaration checks |
| --- | ---: |
| Original scalar inclusion and C5 input/current/dictionary namespaces | 230 |
| First-word/full-relation mixed-wave foundations and C5 wave values | 111 |
| Mixed first tensors, marked pairing and multilinear first fields | 63 |
| Extended C5 actual-source upper/lower, completeness and native consumers | 739 |
| Total | 1143 |

The last inventory's individual namespace counts are 183 Weyl/direction,
35 first tensor, 11 whole source, 18 Lorentz upper, 19 wave sum, 260 marked
internal controls, 40 internal lift/IBP, 25 even values/coordinates,
11 whole-grade upper, 20 wave words, 13 moments, 8 Lorentz invariance,
20 internal field tensors, 15 internal invariance, 8 admitted wave,
21 completeness and 32 completed native consumers.

Only propext, Classical.choice and Quot.sound are allowed transitively.
Math rejects Physics/GUT imports; Physics rejects GUT module imports.
Nonempty-inventory gates remain. No sorry, custom axiom, native reduction,
audit exception or dependency-pin change is used. No rank, moment,
projection, source-spanning or invariant-extension hypothesis is left in
the public completeness theorem.

The final serialized full lake build passes **8004 jobs**. Accepted new
sources have no tactic/linter warnings. Existing direct mathlib imports
retain their module-system import advisories. The full build also replays
pre-existing deprecation, unused-simp/tactic and declaration-style warnings
in unrelated modules; these do not belong to the C5 additions.

## Reproducible resource envelope

Lean checks retain cores 0,1, two compiler threads, a 16 GiB address-space
guard, default elaboration/kernel/recursion limits and 180/540-second
focused/full ceilings. Builds are serialized. This is a warm-dependency
record, not a clean-cache timing estimate.

```sh
bounded() (
  current_seconds="$1"
  shift
  ulimit -v 16777216 || exit 1
  taskset -c 0,1 timeout "$current_seconds" "$@"
)
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsUpper
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsWaveInternalFields
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsWaveInternal
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsWaveInvariant
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsCompleteness
bounded 180 lake build Physics.FieldTheory.Jets.WeylHiggsCompleteLiterature
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedScalarInclusion.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsCurrent.lean
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedFirstWaves.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsWaves.lean
bounded 180 lake env lean -j2 Math/Algebra/Audit/AuditMixedFirstTensor.lean
bounded 180 lake env lean -j2 Physics/FieldTheory/Jets/Audit/AuditWeylHiggsFirstCompletion.lean
bounded 540 lake build
python3 tools/derivative-literature/generate-weyl-direction-control.py
python3 tools/derivative-literature/generate-higgs-first-control.py
python3 tools/derivative-literature/check-weyl-higgs-finite.py
python3 tools/derivative-literature/check-weyl-higgs-literature.py
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Earlier heartbeat/thread failures were repaired by bounded decomposition,
named field/slot identities, explicit grading arguments and individual
generated-module builds. The accepted proofs keep the same limits; those
attempts are not a mathematical stop. The two generators reproduce their
checked Lean sources without changes.

## Independent validation and repository checks

The pinned Li/Murphy/DHM primary displays were rechecked. Completed Lean
consumers verify normalized native values, both inverse laws,
generated/component agreement, nonzero full-quotient support and deliberate
factor/sign errors. Exact Gaussian-rational/Grassmann diagnostics also pass;
the simulated local Li discrepancy does not prevent Murphy or DHM checks.
The finite rank and EOM/IBP omission controls remain independent diagnostics.
Counts and precise paper boundaries are in [literature validation](literature-validation.md).

Layout passes for 2508 modules. Every source and strict audit is registered
in its layer aggregate. Topic/outcome navigation covers all 165 topics.
Portable metadata passes for 1261 documents/evidence files. Local links
pass for 1269 Markdown files, 8184 inline links and 156 heading fragments;
git diff --check passes. Bibliography, proof/assumptions dossiers and derivative/Li
coverage describe the completed fixed-sector theorem. The root README,
published inputs and dependency pins remain unchanged. The subsequent
[master integration](master-integration.md) repeats the proof checks on the
merged state and records the final documentation gates. No remote update
was performed.
