# Structural block continuation verification

This is an earlier partial checkpoint. The completed Li source/orbit
replacement is recorded in [the current result](source-replacement-results.md)
and [its verification](source-replacement-verification.md).

## Acceptance and trust boundary

The new block and exchange modules must not import the dense finite-data,
orbit-table or basis modules. The existing strict decomposition audit now
checks twenty declarations and rejects these imports. The same three-axiom
allowlist is retained. No dependency pin, numerical-proof exception or proof
limit was raised. `LiSixQuarkFiniteData` remains unchanged and was not directly
re-evaluated. The old selected-orbit certificate remains active and is not
claimed retired.

All bounded Lean commands use one Lean thread, a 10 GiB sampled process-group
RSS guard, 4 GiB host-memory reserve and 300-second budget per invocation.
No retired numerical source is a build target.

## Focused results

- Rewritten `LiSixQuarkExtension`: 3,276 jobs, 11.0 seconds, sampled peak
  4,448,816 KiB. The extra array is factored and its invariance is proved by
  small block actions and symbolic tensor transport.
- `LiSixQuarkExchangeBlocks`: initial direct check passed in 4.0 seconds,
  sampled peak 4,271,300 KiB. A generic swap-twice lemma avoided an initial
  default recursion-limit failure caused by unfolding the concrete reconstructed
  coefficient. No recursion limit was raised.
- `LiSixQuarkPairBlock`: 3,277 jobs, 4.5 seconds, sampled peak 4,355,892 KiB.
- Final expanded audit build including the product coordinates: 3,284 jobs,
  10.3 seconds, sampled peak 4,668,048 KiB, twenty strict transitive checks.

Intermediate elaboration errors and an unused-tactic warning were corrected
before acceptance. Final focused targets have no warnings. The new proofs use
symbolic ring/module reasoning and small coordinate cases; explicit scalar
arithmetic is retained and is not described as absent.

## Final checks

The full default-target build passed: 7,420 jobs, 206.4 seconds, sampled peak
8,213,644 KiB, no warnings or errors. The existing semantic seed dictionary,
selected basis, residual consumers, four-flavor witness and printed-flavor
boundary were rebuilt successfully after the factored definition of `extra`.
No memory guard triggered in the accepted continuation checks.

The final audits were run directly with `lake env lean` through the bounded
runner, sequentially after the build:

| Audit | Strict checks | Seconds | Sampled peak KiB |
| --- | ---: | ---: | ---: |
| `AuditLiSixQuarkProbeDecomposition` | 20 | 3.8 | 4,611,332 |
| `AuditLiSixQuarkBasis` | 18 | 3.5 | 4,603,588 |
| `AuditLiSixQuarkFlavorBoundary` | 13 | 3.8 | 4,624,516 |

All 51 fresh checks passed. Cached audit messages in the full build are not
counted as fresh checks. The first audit also enforces the dense-certificate
import exclusions for the new structural modules.

Layout passed for 2,034 modules. Retirement checks passed 19 source hashes
and confirmed 15 retired modules absent with no active imports. Metadata
checks passed 1,082 portable evidence files. Topic coverage passed 146 topics
and 146 outcome links. Local links passed 1,090 Markdown files, 6,812 links
and 111 heading fragments, with no errors. Whitespace checks passed.

The source of `LiSixQuarkFiniteData` was compared byte-for-byte against the
starting checkpoint and is unchanged. Its old left/right inverse and seed
coordinate numerical proofs have not been removed. No claim of a complete
numerical-proof elimination is made. The resource-intensive full downstream
rebuild was performed once for this coherent continuation; further replacement
should remain in small modules until another coherent milestone is ready.
No merge or push is authorized.
