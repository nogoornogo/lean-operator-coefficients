# Mixed-color contraction verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-contraction-results.md).

Focused builds use one Lean thread, a 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap. No dependency or proof limit
changes are made.

- `SL2SpannedProducts`: pass, 5.0 s, peak 4,772,724 KiB.
- `SL3CompactComparison`, including complex coordinate planes: pass,
  10.8 s, peak 4,927,032 KiB.
- `SU3BalancedContractions`, including perfect tensor curry and actual
  SL3 permutation commutant: pass, 4.5 s, peak 4,863,800 KiB.
- `TensorVolumeSplit`: pass, 4.8 s, peak 3,809,952 KiB.
- `SU3VolumeContractions`: pass, 4.8 s, peak 4,877,668 KiB.
- `TensorContractionSpan`: pass, 4.0 s, peak 3,815,532 KiB.
- `SU3MixedContractionSpan`, including inverse-transpose dual transport
  and tensor-power equivalences: pass, 5.0 s, peak 4,890,844 KiB.
- Final structural Math audit also builds `InvariantSpanningRestriction`:
  all 1368 strict transitive checks pass, 7.0 s, peak 5,374,516 KiB.
  This adds 104 audited declarations in thirteen registered modules.
- Physics structural audit: all 306 checks pass; unchanged cached consumer
  replay, 2.5 s, peak 877,504 KiB.

The guarded default `lake build`, including Math, Physics and GUT, passes
all 7258 jobs in 8.8 s, peak 6,648,212 KiB, with zero warnings/errors and no
resource guard triggered. Its guard uses a 10 GiB sampled process-group cap,
4 GiB host reserve and 300-second wall cap. Successful focused logs are also
warning-free. Disposable logs and monitor output remain under `/tmp`.

Layout passes 1872 modules. Local links, retired-certificate checks and
whitespace checks pass. The retirement check verifies 19 hashes and confirms
15 retired numerical modules remain absent. New-module proof-token and
proof-limit scans are clean; the structural audit's numerical import
exclusions and axiom allowlist remain unchanged.
