# Flag and vertex verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [results](colored-flag-vertex-results.md).

Focused checks use one Lean thread, a 6 GiB sampled process-group RSS cap,
4 GiB host reserve and 300-second wall cap. No proof limit or dependency changes.

- `ColorFlagNonvanishing`: pass, 3.8 s, peak 3,399,844 KiB.
- `SymmetricTensorSplit`: pass, 4.3 s, peak 4,399,172 KiB.
- `SymmetricTensorTrace`: pass, 4.8 s, peak 4,417,844 KiB.
- `RestrictedColorTraces`: pass, 7.8 s, peak 4,781,636 KiB.
- `SymmetricPowerDualEquivalence`: initial perfect-pairing check passes,
  4.5 s, peak 4,425,596 KiB; its unused-hypothesis warning was then removed
  and the warning-free source rebuilt with the dual-kernel dependency check.
- `RestrictedColorDuality`, including the generic cancellation helper and
  all three kernels plus trace-free endomorphisms: final pass, 5.0 s,
  peak 4,744,492 KiB.
- `RestrictedColorVertices`, including exact flag embeddings: final pass,
  5.8 s, peak 4,759,936 KiB.

The first dual-kernel comparison elaboration reached the unchanged 200000
heartbeat limit while converting additive group dictionaries. The helper
was rewritten to accept original additive monoids and `Module.Finite`,
then construct the two groups needed inside cancellation. This preserves
the mathematical statement and avoids repeated carrier expansion. No
heartbeat increase or numerical fallback was used. Explicit kernel carrier
wrappers similarly keep subsequent source rewrites local.

Eight modules and 98 strict declarations are registered. Math passes all
1466 strict transitive checks, 6.5 s, peak 5,379,676 KiB. Physics passes all
306 unchanged checks by cached replay, 2.5 s, peak 877,740 KiB. The numerical
import exclusions and strict axiom allowlists remain unchanged.

The guarded default `lake build`, including Math, Physics and GUT, passes
all 7266 jobs in 8.8 s, peak 6,643,128 KiB, with zero warnings/errors and no
resource guard triggered. Its guard uses a 10 GiB sampled process-group cap,
4 GiB host reserve and 300-second wall cap. Final successful focused logs
are warning-free. Disposable output remains under `/tmp`.

Layout passes 1880 modules; local links pass 940 Markdown files, 5779 links
and 111 fragments with zero errors. The retirement check passes 19 hashes
and confirms 15 retired modules remain absent. Proof-token/limit scans and
`git diff --check` are clean.
