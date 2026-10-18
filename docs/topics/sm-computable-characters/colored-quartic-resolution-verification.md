# Q quartic color/weak verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See the [continuation plan](colored-support-completion-plan.md)
and [proved result](colored-quartic-resolution-results.md).

## Resources and trust

Focused checks use the existing `tools/exact-rank/kernel-probe.py`,
serialized with `LEAN_NUM_THREADS=1`, a 6 GiB sampled process-group RSS
cap, 4 GiB host reserve and 300-second wall-clock cap. The full build
uses the same monitor with a 10 GiB cap and
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`.
No dependency pin or Lean proof limit is changed.

The structural audit registers 142 new Math declarations from thirteen
new modules, plus four actual Physics endpoints. Its layer/original-module
checks and numerical-evaluator/certificate import exclusions are unchanged.
The strict transitive allowlist still contains only `propext`,
`Classical.choice` and `Quot.sound`.

The new identities use arbitrary vectors, actual quotient sections,
tensor duality and finite common-summand cancellation. Concrete color
coordinates occur only in normalized nonzero witnesses for the defining
and dual contraction kernels, not in rank or multiplicity evaluation.
Generic dimensions remain symbolic; fixed doublet/slot structure is
part of the universal source maps. No SM content table is expanded.

## Focused evidence

Command form:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.LinearAlgebra.SymmetricFourth22`: passed, including all shuffle,
  annihilation and inverse identities; 11.5 s, peak 4,877,052 KiB.
- `Math.RepresentationTheory.SymmetricFourth22`: passed; its later
  small-dimension kernel identification rebuilt successfully with the
  color modules.
- `Math.LinearAlgebra.SymmetricSquareContraction`: passed with the
  canonical section and actual nonzero-kernel witness; final focused
  run 5.8 s, peak 4,337,744 KiB.
- `Math.RepresentationTheory.SymmetricSquareContraction`,
  `SymmetricExteriorSquare`, `DefiningTraceFreeProduct`,
  `ScalarSymmetricSquare`, `SU3QuarticColor`, `DoubletQuartic`,
  `SymmetricSquareSum` and `SymmetricSquareDual`: passed. The last
  duality check took 4.5 s, peak 4,337,492 KiB.
- `Math.RepresentationTheory.ColorWeakQuartic`: both resolved kernels
  and the complete quartic equivalence passed; 13.0 s, peak
  4,962,632 KiB, with the subsequent dependency rebuild also passing.
- `Math.RepresentationTheory.SU3DoubleSpinQuartic`: actual positive,
  negative and both degree-eight equivalences passed.
- `Physics.StandardModel.Operators.SMQQuarticBranching`: all four
  actual core transports passed; final rebuild in the Physics audit.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  963 strict transitive checks passed; 9.0 s, peak 5,329,944 KiB.
- `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`:
  300 strict transitive checks passed; 10.8 s, peak 5,449,352 KiB.
  The combined structural count is 1263. Neither guard triggered.

Earlier failed elaborations are not proof evidence. Additive-group
carrier ambiguities and coercion mismatches were resolved by explicit
compatible carriers and smaller application identities. No limits or
audit exclusions were relaxed. Final focused logs contain no warnings.

## Aggregate and repository acceptance

- Guarded default `lake build`: passed, 7200 jobs, including rebuilt
  Math, Physics and GUT aggregates; 11.3 s, observed process-group peak
  6,627,240 KiB. No guard triggered and no warning/error remained.
- `node tools/layout/check-layout.mjs`: passed, 1824 modules.
- `node tools/docs/check-links.mjs`: passed, 920 Markdown files,
  5702 local inline links and 111 fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: passed,
  19 snapshot hashes intact, 15 retired modules absent, imports clean.
- Source forbidden-token/proof-limit and pin/retirement boundary review:
  passed. Root README is unchanged.
- `git diff --check` and final staged whitespace review: passed.

Temporary logs and the guarded default-build runner remain outside source
control. The accepted full build imports both persistent structural audits.

## Scope

The quartic color/weak source identity and its actual Q/conjugate-Q
degree-four/eight transports are proved. H is an actual nonzero
contraction-kernel color factor; no general irreducibility or product
rule for H is asserted. Degree-five/six joint branching, compatible
general restricted-color coupling and the original complete mixed q/l
support iff remain obligations of the continuation.
