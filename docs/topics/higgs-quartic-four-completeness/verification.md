# Verification by milestone

## Candidate invariance and full-relation separation

The initial focused source checks pass under the frozen two-core/two-thread,
16 GiB address-space, default elaboration/kernel and 180-second focused
limits. The following persistent strict audit build passes 3762 jobs:

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.Algebra.Audit.AuditColoredFourWaves \
  Physics.FieldTheory.Jets.Audit.AuditHiggsQuarticFour
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
```

The strict transitive inventories cover 110 declarations: colored waves 14,
actual input 39, full Higgs wave relations 7, and quotient separation 50.
Only propext, Classical.choice and Quot.sound are allowed, with layer-import
restrictions and nonempty inventories retained. The serialized full build
passes 7793 jobs. Layout passes 2297 modules; all six new proof/audit modules
are registered in Math.lean or Physics.lean. Accepted new sources have no
tactic/linter warnings; inherited module-system import advisories remain.

The independent standard-library [Higgs diagnostic](../../../tools/derivative-literature/check-higgs-four.py)
passes the three-by-three quotient value matrix, 15504 colored divergence
checks, 16 Li-density readings and 384 simultaneous wave-label permutations.
Its explicit nullness/conservation-removal and omitted-candidate controls
detect the removed conditions. These calculations are not Lean premises.
At this initial checkpoint they were investigative comparisons pending the
final literature queue, without a whole-grade completeness claim. The
complete endpoint below owns the subsequent proof and comparison gates.

## Complete coefficient and literature endpoint

All 105 ordered-moment modules (`R0M0` through `R2M34`) pass separately.
Their 420 component-family theorems use kernel reduction for the paired
entries and proved coordinate-sign closure for the remaining entries.
The sorted-family, four wave-slot and complete moment assemblies pass.
Both generators reproduce all 120 generated Lean files byte for byte in a
temporary output tree; generated tables are never trusted proof premises.

The entire-source upper bound, closed normalized coefficients, both inverse
laws, dimension 3, direct/generated agreement and native literature
consumers pass focused builds. The public module has no moment hypothesis
for the caller. The four strict audits are then freshly elaborated:

| Audit | Strict transitive declaration checks |
| --- | ---: |
| `Math/Algebra/Audit/AuditColoredFourWaves.lean` | 14 |
| `Physics/FieldTheory/Jets/Audit/AuditHiggsQuarticFour.lean` | 96 |
| `Math/Algebra/Audit/AuditHiggsQuarticFourFoundations.lean` | 4923 |
| `Physics/FieldTheory/Jets/Audit/AuditHiggsQuarticFourCompleteness.lean` | 586 |
| Total | 5619 |

These are complete namespace declaration inventories, including generated
helpers, not counts of independent mathematical theorems. Only propext,
Classical.choice and Quot.sound are allowed. Import-layer and nonempty
inventory checks pass. There is no sorry, custom axiom, native reduction
allowance, widened audit exception or dependency-pin change. Accepted new
sources have no tactic/linter warnings; existing-style mathlib module-system
import advisories remain, including the new Gaussian/multilinear imports.

The final serialized full build passes **7947 jobs**. Every check retains
two compiler threads, cores 0,1, a 16 GiB address-space guard and default
elaboration/kernel/recursion limits. Focused and full ceilings remain
180 and 540 seconds. This is a warm-dependency verification record, not
a clean-cache time or universal memory estimate.

One aggregate attempt restarted several dependency compilations at once
and failed to create a thread. Building the four internal-case modules,
their consumers and the moment/coefficient modules one at a time resolves
it under the same limits. Earlier vector lookup depth and direct expansion
of constructed coefficient values were resolved by balanced data lookup
and named coordinate/extraction laws. No failed attempt is counted as a pass.

The session used a Python `RLIMIT_AS` wrapper. An equivalent Bash guard,
without that temporary helper, is:

```sh
bounded() (
  higgs_seconds="$1"
  shift
  ulimit -v 16777216 || exit 1
  taskset -c 0,1 timeout "$higgs_seconds" "$@"
)
bounded 180 lake build Math.Algebra.HiggsFourWaveCubature.R0M0
# Build each remaining RrMm and bounded assembly module separately.
bounded 180 lake build Physics.FieldTheory.Jets.HiggsQuarticFourCompleteness
bounded 180 lake build Physics.FieldTheory.Jets.HiggsQuarticFourLiterature
for higgs_audit in \
  Math/Algebra/Audit/AuditColoredFourWaves.lean \
  Physics/FieldTheory/Jets/Audit/AuditHiggsQuarticFour.lean \
  Math/Algebra/Audit/AuditHiggsQuarticFourFoundations.lean \
  Physics/FieldTheory/Jets/Audit/AuditHiggsQuarticFourCompleteness.lean
do
  bounded 180 lake env lean -j2 "$higgs_audit" || exit 1
done
bounded 540 lake build
python3 tools/derivative-literature/check-higgs-four.py
python3 tools/derivative-literature/check-higgs-literature.py
```

The primary Murphy, Li and Eboli PDF displays were inspected visually at
their pinned locations. The actual-input Lean consumers and independent
exact diagnostics agree for all three native dictionaries. Each paper has
16 rational-configuration/color-assignment checks and tested rank 3. An
intentionally wrong Li factor produces a local discrepancy while the next
Eboli check still passes. The other diagnostic passes 15504 divergence
checks, 16 literal Li readings and 384 simultaneous wave permutations;
nullness/conservation-removal and omitted-density controls are detected.
These are diagnostic evidence, not Lean premises. The full per-source
scope is in [literature validation](literature-validation.md).

Layout checks cover 2451 modules. Default topic/outcome navigation,
portable metadata, local links and whitespace checks pass. The topic is
complete on its recorded working branch and remains unmerged. No master
integration or remote update is included in this endpoint.

The subsequent authorized master integration and its fresh merged-state
verification are recorded separately in [integration](integration.md).
