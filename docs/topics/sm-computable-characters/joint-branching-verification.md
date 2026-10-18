# Joint branching verification

Branch `proof/sm-computable-characters`, starting from `checkpoint 01`. All proof
builds are serialized, use `LEAN_NUM_THREADS=1`, and run under the existing
guard without increasing Lean options or resource limits:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/joint-MODULE.log
```

The default timeout is 300 seconds. RSS is sampled for the whole child process
group; it is a diagnostic guard, not a proof input or a hard cgroup limit.
Temporary logs and probes are not committed.

## Focused proofs and strict audits

The final colored-target build passed with all new dependencies, 4449 jobs,
19.8 seconds and sampled group peak 5148936 KiB. After isolating the general
character dependencies from closed rank certificates, the final optional
audit rebuild below checks that refinement as well.

| Audit | Checks | Result | Time | Sampled group peak (KiB) |
| --- | --- | --- | --- | --- |
| `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport` | 93 | passed, 4075 jobs | 5.0 s | 5219400 |
| `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport` | 178 | passed, 4384 jobs | 5.5 s | 5382292 |
| `Physics.StandardModel.Operators.Audit.AuditSMJointAlgebraicSupport` | 25 | passed, 4431 jobs | 32.3 s | 5403356 |

These **296 strict transitive checks** permit only `propext`, `Classical.choice`
and `Quot.sound`. The two structural audits retain their original evaluator
import rejection. The new optional extraction audit accepts generic character
correctness but rejects closed rank/multiplicity certificate imports. Its
Weyl consumers remain explicit conditional implications.

The new optional audit initially rejected a transitive `LLHHKernelRank`
import. Investigation found `SMIteratedContent` imported `SMConstantContentRanks`
only for its small species-dimension dictionary. The general interface now
uses the definitionally identical dictionary directly and imports the needed
generic charged/parity lemmas. The new consumer also imports the character
construction directly. The unchanged strict rejection then passed; no
allowlist was weakened and no old numerical certificate was used.
The first Physics aggregate exposed `SMNeutralSparseRanks`' reliance on that
former transitive import. Giving this existing numerical consumer its own
direct `SMConstantContentRanks` import preserves its statements/proofs and
keeps the new symbolic consumer's strict dependency rejection intact. The
subsequent Physics aggregate passed.

During development, concrete nested Hom/presentation simplification reached
the default heartbeat limit. Abstract `presents_of_characters` and
`terms_balance` transports keep the representations and polynomial data
opaque; the final colored module builds in 6.7 seconds. Naming intermediate
tensor-product analytic structures similarly avoids deep instance search.
There was no raised heartbeat/recursion option, expanded closed character,
exact rank numeral or new external theorem premise.

## Aggregate and repository verification

Aggregate builds also set `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, as in the preceding checkpoint, without
changing the guard or proof options.

| Target | Result | Time | Sampled group peak (KiB) |
| --- | --- | --- | --- |
| `Math` | passed, 6027 jobs | 6.3 s | 6205064 |
| `Physics` | passed, 5045 jobs | 19.3 s | 5671072 |
| `GUT` (configured default library) | interrupted at unchanged 6 GiB threshold | 5.3 s | 6401136 |

The final Physics check also rebuilds the affected existing consumers and
their strict audits. Final successful focused/aggregate logs have no warnings
or errors. This does not treat a conditional theorem's Weyl premise as proved.

Repository checks:

- `node tools/layout/check-layout.mjs`: 1709 modules; layers, imports, cycles,
  aggregate coverage and relocations passed.
- `node tools/docs/check-links.mjs`: 881 Markdown files, 5466 local links,
  109 fragments, zero errors, including the updated proof dossier.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot hashes
  match, 15 retired modules absent, active imports clean.
- The fourteen new theorem modules contain no `sorry`, custom axiom,
  `native_decide` or `implemented_by`. `git diff --check` passed.

The GUT attempt reached the root/default aggregate after replaying its checked
dependencies and was interrupted by the guard. This is **not a successful
full `lake build`**. The previously recorded root aggregate resource gate
remains; it is independent of the joint occurrence theorem and no unchanged
retry or increased budget was used.

The final `lake --no-build build Math Physics` also naming the three strict
audit roots passed, with all targets up to date (6626 jobs). The default
`lake --no-build build` returned 3 with exactly `GUT` stale in its 7077-job
graph. No new proof module or other dependency is left unbuilt in that graph.
`git diff --check` and the final staged diff check passed. Source/statements,
assumptions, conditional input boundaries and dossier agreement were reviewed
before committing the verified milestone on the existing topic branch.

The proof endpoint is a uniform conditional algebraic criterion, not an
enumerated table of concrete decisions. Its source/target presentations and
structural decompositions are proved; Weyl reduction remains explicit.
Lean/dependency pins, root README, CSV outputs and retired archives are
unchanged. No merge or push is made.
