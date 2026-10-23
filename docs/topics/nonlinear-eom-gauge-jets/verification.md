# Verification

Working branch: `proof/nonlinear-eom-gauge-jets`; integration target:
`proof/derivative-ibp`, under the bounded-child exception. The initial parent
worktree was clean. No parent/master integration or remote mutation is included.

## Contract And Proof Checks

The three-stage contract was recorded before implementation. The direct
derivative-word ideal, associative commutator and entrywise matrix routes
close all stages. No fallback intersection construction or independent
normal-form foundation is required. No `sorry`, custom axiom, imported
physical covariance, new dependency or audit allowlist exception is used.

Focused final command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditNonlinearGaugeJets Physics.FieldTheory.Jets.Audit.AuditNonlinearGaugeJets
```

Passed: 3283 jobs, with 72 Math and 74 physical public declaration checks,
146 total. The persistent audits contain explicit inventories of the eight
implementation files' named public definitions, abbreviations, structure,
theorems and instances, and collect axioms transitively. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The Math audit rejects
Physics/GUT imports and the physical audit rejects GUT imports. All ten new
implementation/audit modules are registered in the appropriate aggregates.

The checks cover minimal/stable differential ideals, exact kernels, descended
derivations, inverse source/coefficient EOM/IBP comparison, finite images and
linear recovery; actual scalar seed/ideal Lorentz invariance and the interacting
kinetic identity; derived curvature commutator/Bianchi and constant conjugation;
actual entrywise matrix derivatives; polynomial Yang–Mills EOM with ordinary
and covariant descendants; surviving EOM units; and a nonzero nonlinear
off-shell equation that vanishes after projection.

Earlier matrix elaboration trials reached the default 200000-heartbeat limit.
Typed entrywise equalities and explicit finite-sum proofs close those goals
without raising heartbeats, recursion/kernel limits or adding hypotheses.
The final successful focused run has no new linter/deprecation warnings;
new residual warnings are module-system import recommendations. Existing
project warnings remain unchanged.

## Full Build And Structural Gate

```sh
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
```

The final full build passes 7653 jobs, including Math, Physics, GUT and every
old/new persistent audit. Layout passes for 2159 modules, including layers,
local imports, cycles, aggregate coverage and relocation audits.

Heavy commands are serialized with four Lean threads, a 540-second command
timeout and an inherited 16 GiB per-process address-space limit. This is a
resource guard, not a measured universal memory bound or elapsed-time estimate.
Disposable logs and the guard wrapper remain outside source control.
Root README and all dependency pins are unchanged. Existing proofs and audits
are preserved; only their aggregate import lists gain the new modules.

## Documentation And Final Review

```sh
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The result, mathematical/physical dossiers, source register and assumption
ledgers agree. The literature list records the final inspected source role
and result links before any future integration. No literature-comparison
coverage row or source-wide completeness claim is added.

Final documentation gates pass: 1155 Markdown files, 7371 local inline links,
125 heading fragments and zero link errors. The unchanged link checker runs
where its read-only Git subprocess is permitted. All 153 topics have indexed
outcomes, with no pending exceptions. Portable metadata passes for 1147 files.
The diff is whitespace-clean; root README, dependency pins and coverage
ledgers are unchanged. The explicit audit inventories match all named public
declarations in the eight implementation files.

The final integration/status records are documentation only after the
successful proof gates; no further Lean build is run for those edits. The
successful stop is the completed three-stage formal algebraic contract on
the child branch. SU(N) restrictions, arbitrary local gauge transformations,
analytic/variational dynamics, matrix-model Lorentz dictionaries, general
counts and phenomenology are explicit separate boundaries. No parent/master
merge, remote update or further foundational topic is started at this stop.

## Final Master Integration

The [merged-state record](../derivative-ibp/master-integration.md) supersedes
the earlier unmerged integration status. The original proof endpoints and
checks above remain checkpoint evidence; all recorded parent merges and the
master merge are verified without changing theorem assumptions.
