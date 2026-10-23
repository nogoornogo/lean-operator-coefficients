# Compact occupation decisions for structural SM support

The fixed signed three-generation SM support criterion has opt-in finite
kernel decisions with a compact generation-occupation enumeration. These
preserve the original propositions; they are not a new support classification
or a general compiled request solver.

## Mathematical enumeration

[Math.CompactGenerationOccupations](../../../../../Math/RepresentationTheory/Exterior/CompactGenerationOccupations.lean)
proves attainability iff the three counts sum to n. The reverse direction
constructs an actual contiguous generation word with the requested counts.

The dependent index

```text
Index n = Sigma (a : Fin (n+1)), Fin (n-a.val+1)
```

is equivalent to the existing `GenerationTensorSupport.Occupation n` by
`equiv`. `fintype` transports its finite enumeration without imaging all 3^n
words or executing deduplication of count vectors. `choiceFintype` explicitly
uses compact occupations at every leaf of an arbitrary existing content tree.
It is not registered as a replacement global instance. No representation,
statistics, residual action or coefficient-space comparison changes.

## Physics consumer and closed checks

[SMCompactSupportDecision](../../../../../Physics/StandardModel/Operators/Support/Decomposition/SMCompactSupportDecision.lean)
provides named `contentDecision` and `higgsDecision`. They return `Decidable`
for the **same** `SMJointContentSupport.Supports` and
`SMJointHiggsSupport.HiggsSupport` predicates. Local helpers decide the finite
owner, path and expression conditions. A caller opts in explicitly, for example
with a local instance attribute on `Physics.SMCompactSupportDecision.higgsDecision`.
Previously elaborated default decisions do not automatically change.

The definitions remain noncomputable for compiled execution because they
project metadata from proof-bearing actual presentations. Closed kernel
checks work; no global `#eval` support solver or generic fast negative-search
bound is claimed. Subsequent [107-sign certificates](../../../../topics/sm-support-evaluator-feasibility/remaining-checks-results.md)
and [572-assignment certificates](../../../../topics/sm-support-evaluator-feasibility/assignment-results.md)
use symbolic exclusions and explicit witnesses in reproducible diagnostic
files. Those fixed-domain checks preserve actual coefficient semantics but
do not provide a general compiled evaluator.

[SMCompactSupportExamples](../../../../../Physics/StandardModel/Operators/Support/Decomposition/SMCompactSupportExamples.lean)
proves actual original-space statements at k=1,q=l=0:

- `q18Allowed`: Q^18 with h=0,d=6 is allowed.
- `mixedForbidden`: Q/conjugate-Q at h=d=0 is forbidden, despite neutral
  residual and hypercharge conditions, by the full structural predicate.

Both use `original_ql_iff` or its prohibition counterpart and `decide +kernel`.
No Weyl input, rank, numerical table or supplied occurrence premise is added.
Permission means a nonzero invariant coefficient, not a generated interaction
or a rate. Derivatives/EOM/IBP, other Higgs/residual inputs and UV realization
remain outside these examples.

## Verification scope

Persistent Math/Physics audits check all named new interfaces and examples
against propext, Classical.choice and Quot.sound, without exceptions. Focused
builds and strict audits pass. The user-authorized 10 GiB full-build check
passed all 7325 jobs with zero warnings/errors, after the earlier 6 GiB guard
interruption. Individual closed checks retained their 6 GiB ceiling and Lean
options were unchanged. No merge is claimed. See the
[implementation record](../../../../topics/sm-support-evaluator-feasibility/implementation-results.md)
for exact measurements, rejection tests and remaining gates.

## Subsequent executable metadata boundary

A [mathematical data layer](../Math/JOINT_SOURCE_DATA.md) supplies executable
core metadata and generic composition with ordinary correspondence proofs.
The [revised SM connection](SM_JOINT_SUPPORT_DATA.md) now proves support/Higgs/
original-space equivalence and checks ordinary downstream consumers under the
10 GiB/120-second guard. The earlier interrupted projection comparison is
retained as [stop evidence](../../../../topics/sm-support-evaluator-feasibility/data-layer-results.md),
not a current unproved bridge. General compiled decision functions and raw
search performance remain unchanged.
