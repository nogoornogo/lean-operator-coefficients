# Source API Compatibility Verification

The original source-refactor endpoint was verified on `refactor/source-api-compatibility`.
The later authorized [master integration](master-integration.md) includes its
completed children and records separate merged-state checks. Mathematical statements, hypotheses,
dependency pins, proof limits and strict axiom allowlists are preserved.

## Final Acceptance

| Check | Result |
| --- | --- |
| Serialized `lake build Physics`, `lake build GUT`, then default `lake build` | All pass; final default build: 9,723 jobs |
| Complete protected API metadata and per-alias strict checks | 1,677 deprecated import routes; 12,989 protected aliases; canonical Physics ownership and imports pass |
| Legacy consumers | Polymorphic records, projections/dot notation, construction/patterns, cases/induction, coercions, instances, simp, executable eliminators, nonderivative inputs and repeated restriction methods pass |
| Mechanical source replay | 4,218 frozen source paths, five separately reviewed utility/consumer files and three aggregate imports match; no unregistered library changes |
| Elaborated symbol comparison | All 2,540 canonical target modules preserve reference sets and occurrence order; the reviewed proof split preserves its definitions and statement |
| Existing strict-audit inventory | 422 count records verified, including three exact compiler-helper reconciliations; public parent declarations remain audited |
| Previous Math namespace inventory | 1,984 Math modules and 4,227 historical correspondences verified, with two recorded pre-baseline renamings; no legacy Math-owned declarations |
| Layout | 4,226 modules; layers, cycles, local imports, aggregates and historical import exclusions pass |
| Tool regressions | Three migration tests and the layout/origin regression suite pass |
| Generated sources | Eight generators reproduce 144 canonical outputs byte for byte without repository writes |
| Existing derivative diagnostics | Nine finite diagnostic scripts pass; source-reading dimension tools use canonical paths |
| Documentation | Local links, topic navigation, portable metadata and whitespace checks pass |

All Lean/build commands retain two threads, a 16 GiB address-space cap and a
540-second timeout. Bounded warm retries during the rebuild reused checked
artifacts when the timeout was reached with fresh progress. The concluding
Physics/GUT/default sequence passes in one attempt per stage. After intermediate
namespace edits were restored to the recorded source replay, all 447 GUT module
traces and the import-origin trace were invalidated; every GUT module was freshly
rebuilt before acceptance.

Residual warnings include module-system import notices from dependencies,
existing linter/style warnings, and expected deprecation warnings in legacy
consumers and aggregate imports. No warning is treated as proof of a premise.
The final build and strict audits have no errors.

The frozen source transformation is reproducible with
`PYTHONDONTWRITEBYTECODE=1 python3 tools/layout/check-source-transform.py`.
After a complete build, run `check-source-api.py` and
`node tools/layout/check-math-namespaces.mjs`. Reference comparison additionally
requires the saved pre-migration `.ilean` metadata snapshot:

```sh
python3 tools/layout/check-source-references.py /tmp/source-api-baseline-metadata.json
python3 tools/layout/check-audit-counts.py /tmp/source-api-baseline-build.log /tmp/source-api-acceptance-full-1.log --baseline-constants /tmp/source-api-baseline-constants.json --rebuilt-constants /tmp/source-api-final-constants.json
```

The temporary files are verification inputs/output, not repository proof
premises. `tools/layout/ExportSourceAPI.lean` creates a constant snapshot from a
fully built checkout, with its output selected by `SOURCE_API_EXPORT`.
The original frozen registry remains unchanged; its bounded
[addendum](registry-addendum.json) records the generic shared restriction and
retained GUT torus import carrier. Legacy consumer sources are checked in.

## Reviewed Build And Inventory Repairs

A [controlled follow-up](resource-investigation.md) rebuilds the original and
unrepaired renamed module with fresh local dependencies. Both fail under the
same 16 GiB address-space guard. Earlier baseline/pilot successes reused cached
artifacts; they did not regenerate this source proof in those runs. The namespace
change is therefore not needed to reproduce the failure. Historical initial
compilation conditions and the exact allocator failure site remain unestablished.

The monolithic six-quark `fierz_blockAlternation` expansion exhausted the
unchanged memory guard after relocation. Its unchanged definitions now live in
a basic module, and the exact universally quantified theorem follows by evaluating
an existing independent coordinate Fierz identity on arbitrary pure inputs.
There is no dependency cycle. Its original ten-check strict audit passes.
The [proof-repair record](proof-repairs.json) freezes the statement and seven
lazily realized equation owners. Reference comparison checks all unchanged
definitions and the theorem statement; kernel checking and the original audit
validate the replacement proof.

Eight finite-certificate modules reproducibly failed to create asynchronous
elaboration threads. Their identical declarations, proof bodies, kernel decisions
and limits pass with local synchronous elaboration. The
[scheduling record](execution-repairs.json), generated sources and source replay
agree. Default type/value unification also expanded two very large alias targets;
the compatibility command now checks exact canonical values and exact restoration
of types through genuine direct aliases. Kernel declaration checking and strict
transitive axiom checks remain mandatory, individually under the default budget.
The wrong-target rejection control passes.

Synchronous elaboration changes compiler-generated auxiliary names and sharing.
Three namespace-wide audit counts therefore change from 1,199 to 1,056, 140 to
138, and 288 to 278. The [inventory reconciliation](audit-inventory-repairs.json)
records exact removed/added helper counts and hashes. The checker permits only
proof/match/simp helpers, verifies that every parent remains present, preserves
all protected declarations, and matches both log counts to full constant
snapshots. All audit predicates and axiom allowances remain unchanged.

The older Math namespace inventory retained two names already renamed before
this topic's frozen baseline. Its [spelling corrections](namespace-check-repairs.json)
verify the existing declarations rather than drop the entries. Private macro
names normalize both dotted and compiler-encoded module paths.

## Checked Pilot

The canonical implementation is now
`Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum`, with namespace
`Physics.AbelianMassSpectrum`. The previous import and ten old declaration names
remain deprecated facades/aliases. The [pilot registry](declaration-map.json)
records the exact correspondence; the [full plan](layout-plan.json) freezes the
next batches separately.

- The existing mass-spectrum audit builds with its mathematical statements
  unchanged. Direct and indirect in-repository clients use canonical references.
- `Physics.Compatibility.Audit.AbelianMassSpectrum` checks ten definitional value
  equalities and twenty strict transitive axiom inventories.
- `Physics.Compatibility.Audit.Structures` checks polymorphic record syntax,
  projections/dot notation, constructor patterns, `cases`, coercions, instance
  search, simp and executable data (evaluation returns `7`). Old-name warnings
  are expected in these consumers.
- Ordinary aliases alone failed legacy dot notation and constructor patterns.
  The checked generator preserves legacy heads in argument types and marks
  constructor aliases for pattern matching. Canonical instance/simp registrations
  remain unique. This is a compatibility repair, not a new mathematical premise.
- The first serialized full build exposed two indirect old-name users, then
  reached the 540-second guard while building the changed import-audit graph.
  Their references were corrected and focused consumers passed. The subsequent
  serialized `lake build` passes (8,045 jobs), with the same guards and default
  proof limits. No allowance or dependency pin changed.
- `python3 tools/layout/test-source-api.py`: three migration-tool regressions pass.
  Layout, local links, topic navigation and portable metadata checks pass.

These are the retained pilot checks. Full-registry acceptance belongs to the
current sweep above, rather than to this earlier checkpoint.

## Deprecation Support On The Pinned Toolchain

The installed Lean 4.35.0 sources define declaration deprecation in
`Lean/Linter/Deprecated.lean` and module deprecation in
`Lean/Elab/BuiltinCommand.lean`. Both accept a replacement/message and a `since`
string. The source describes the latter as a date or library version; a real
migration should use its assigned version marker. The artificial test below
uses `probe`, which is not a release designation.

Three isolated files were created in a temporary directory:

`Current.lean`:

```lean
import Mathlib.Init
namespace SourceAPICompatProbe.Current
def value (n : Nat) : Nat := n
end SourceAPICompatProbe.Current
```

`Legacy.lean`:

```lean
import Current
deprecated_module "Use Current instead." (since := "probe")
namespace SourceAPICompatProbe.Legacy
@[deprecated SourceAPICompatProbe.Current.value (since := "probe")]
abbrev value := SourceAPICompatProbe.Current.value
end SourceAPICompatProbe.Legacy
```

`Consumer.lean`:

```lean
import Legacy
example : SourceAPICompatProbe.Legacy.value 7 = 7 := rfl
```

For reproduction, place these files in a temporary directory and set
`probe_dir` accordingly. Run from the repository root so the pinned
toolchain/dependency environment applies:

```sh
probe_dir=/tmp/source-api-compatibility-probe
ulimit -v 16777216
LEAN_PATH="$probe_dir" timeout 540 lake env lean -j2 -R "$probe_dir" -o "$probe_dir/Current.olean" "$probe_dir/Current.lean"
LEAN_PATH="$probe_dir" timeout 540 lake env lean -j2 -R "$probe_dir" -o "$probe_dir/Legacy.olean" "$probe_dir/Legacy.lean"
LEAN_PATH="$probe_dir" timeout 540 lake env lean -j2 -R "$probe_dir" "$probe_dir/Consumer.lean"
```

All three commands exit successfully under the recorded 16 GiB / 540-second
guards. The consumer emits both expected warnings: replace `import Legacy`
with `import Current`, and replace the legacy declaration with the current
declaration. The old call still elaborates and its equality closes by `rfl`.
Lean also notes that a namespace change can require dot-notation adjustments
when callers adopt the replacement name. No warning was suppressed.

These isolated probes check one simple definition. The persistent consumers
above separately check structures, generated names, notation, instances, simp
attributes and the mass-spectrum API.
Temporary Lean files, compiled output and logs are not repository sources.

## Retained Preparation Checkpoint

The initial preparation changed only README and topic/index documents. It
changed no repository Lean declaration, module path, audit or dependency pin.
That checkpoint ran the three isolated language probes without a repository
build. Its checks were:

- `node tools/docs/check-links.mjs`: PASS, zero local-link/anchor errors.
- `python3 tools/docs/check-topic-index.py --pending-topic source-api-compatibility`:
  PASS, with this planned topic explicitly pending.
- `python3 tools/docs/check-work-metadata.py`: PASS.
- `node tools/layout/check-layout.mjs`: PASS, 2,544 modules on this master-based branch.
- `git diff --check`: PASS.
