# SM rank evaluation and q/l enumeration

- Status: deferred
- Result type: proved charged full-rank and cutoff zero-rank formulas;
  reproduced bounded assignment enumeration; neutral all-content ranks open
- Branch: `proof/sm-rank-enumeration`
- Integration target: `proof/sm-statistical-finite-kernel`
- Parent exception: bounded child of the existing unmerged topic.
- Authorization: user requested concrete ranks and the 572-assignment recount.

Master integration was authorized at stage 01 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

## Frozen work and acceptance

1. Reproduce the order 2 through 12 charge domain, its 572 candidates, 151
   fixed-order unit orbits and the existing bounded sector profiles. Export
   every labelled candidate with its orbit representative; compare against
   the existing kernel-checked Lean counts. These are not all-degree counts.
2. Prove full column rank of the actual local constraint matrix whenever
   source hypercharge plus `3*delta` is nonzero. Preserve the actual source
   statistics and matrix definition, including zero-dimensional carriers.
3. Measure the finite table size and inspect the executable-coordinate route.
   The current `Module.finBasis` and complex `exp(i)` entries cannot be fed
   directly to exact Gaussian elimination. Do not silently substitute a Lie
   kernel or numerical tolerance for the actual-group kernel.
4. Continue executable all-content ranks only if a certified, bounded
   coordinate/compression route is available. Stop with the precise missing
   bridge if it requires a new computational representation foundation or
   enumeration beyond lightweight repository-scale computation. Do not
   label a reproduced bounded count as an all-degree reclassification.

Verification: focused builds and strict axiom audit, serialized full build,
layout/link/diff checks, and independent exact standard-library enumeration.
No dependency or resource-limit change. No master merge or push.

## Result and stop

[Results](results.md) record the exact rank formulas, the reproduced CSV and
the computational boundary. [Verification](verification.md) records checks.
The user-requested all-content numerical ranks and rank-based all-degree
reclassification of the 572 assignments are not complete. The next milestone
is the [fixed LLHH rank certificate](../llhh-kernel-rank/README.md), which
connects explicit coefficient coordinates to the actual kernel. Beyond that
fixed content, certified compression is still needed; brute-force enumeration
is outside the repository's lightweight computational scope.

## Sources

- [Finite kernel](../sm-compact-kernel-completion/results.md)
- [Existing count domains](../inverse-cyclic-sm-construction/three-followups-results.md)
- [Actual finite table](../../../Physics/StandardModel/Operators/SMFiniteSupportTable.lean)
- [Actual matrix](../../../Physics/StandardModel/Operators/SMFullLocalKernel.lean)
