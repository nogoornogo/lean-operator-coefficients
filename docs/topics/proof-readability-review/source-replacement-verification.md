# Li source replacement verification

This verifies the actual-source and selected-orbit replacement. Earlier
[block verification](exchange-block-verification.md) records a different,
partial checkpoint and is not the proof baseline for this result.

## Resource and proof gates

All Lean invocations use one Lean thread through
`tools/exact-rank/kernel-probe.py`, with a 10 GiB sampled process-group RSS
guard, a 4 GiB host-memory reserve and 300 seconds per invocation. No
heartbeat/recursion limit or dependency pin was increased. No custom axiom,
`native_decide`, audit exception or incomplete proof was introduced.
The literal source also builds at the default recursion budget: the product
coefficient stays abstract during invariance transport, and the public convention
reuses that single literal definition. The prior recursion setting is not
copied into the new source module.
The original monolithic numerical certificates were removed rather than
re-evaluated to establish the new result.

Broad expansion attempts were revised into explicit application steps,
independent component statements and nineteen source amplitudes. Temporary
elaboration errors and stylistic warnings were corrected before acceptance.
The obsolete stepping-cache interface was retired when its concrete reduction
hit the default recursion limit; the forward matrix is now defined by the
actual orbit recipe, so no independently stored stepping cache is needed.
The generic array-to-matrix agreement is preserved as `orbitR_agrees`.

## Focused accepted checks

| Target | Seconds | Sampled peak KiB | Result |
| --- | ---: | ---: | --- |
| Raw epsilon reconstruction | 4.8 | 4,441,276 | Polynomial identities on arbitrary vectors |
| Uniform Young image profiles | 83.1 | 7,558,328 | Seven image types; no rank table |
| Source directions | 5.8 | 4,421,256 | Nineteen scalar amplitudes; subsequent style cleanup rebuilt cleanly |
| Connected block assembly | 266.8 | 5,005,268 | Arbitrary assembly coefficients; no supplied forward matrix |
| Independent source derivation audit | 23.6 | 7,267,808 | 15 strict checks; excluded certificate imports absent |
| Connected inverse/basis audit | 54.8 | 4,842,400 | 7 strict checks; retired premises absent, including through private helpers |

The accepted full default target (`lake build GUT`, the configured default
library) passed: **7,439 jobs, 83.6 seconds, sampled peak 6,683,392 KiB**,
with no warnings or errors. This includes printed-span/kernel identification,
flavor projection/descent/completeness, the physical four-flavor witness,
residual consumers and the existing other certificate families. Passing their
build does not claim those other numerical certificates have been replaced.

## Fresh final audits and repository checks

The final audits were run directly and sequentially after the last source
cleanup and full build. Their results are recorded below. Cached messages in the full build are not counted as
fresh executions.

| Fresh direct audit | Strict checks | Seconds | Sampled peak KiB |
| --- | ---: | ---: | ---: |
| `AuditLiSixQuarkProbeDecomposition` | 20 | 3.3 | 4,591,124 |
| `AuditLiSixQuarkBasis` | 18 | 3.5 | 4,620,080 |
| `AuditLiSixQuarkFlavorBoundary` | 13 | 3.0 | 4,643,888 |
| `AuditLiSixQuarkSourceDerivation` | 15 | 3.3 | 4,604,184 |
| `AuditLiSixQuarkSymbolicInverse` | 7 | 3.8 | 4,698,932 |

All **73** fresh strict transitive checks passed. Their axiom allowlist remains
`propext`, `Classical.choice`, `Quot.sound`. The source import exclusions and
retired-premise traversal also passed. Final direct runs have no warnings.

Layout passed for 2,053 modules. Retirement checks passed 19 snapshot hashes
and confirmed 15 retired modules absent with no active imports. Metadata
checks passed 1,086 portable documents/evidence files. Topic coverage passed
146 topics and 146 outcome links, with this ongoing topic's pending exception.
Local links passed 1,094 Markdown files, 6,847 links and 111 heading fragments,
with no errors. Whitespace checks passed. The diff and assumptions were
reviewed before the verified Li checkpoint was committed. No merge or push
is authorized; the remaining-family phases continue on this branch.
