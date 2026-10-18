# Complete positive coupling of reachable color factors

Original endpoint 2 remains in progress. The pure-color coupling obligation
is now proved for arbitrary products of all concrete symmetric and
trace-free color factors used by the signed SM core decompositions. The
remaining task is to compose this criterion with all actual species/core,
generation, weak, independent-spin and Higgs/q/l interfaces.

## Actual statement

[`RestrictedColorWordSupport.allowed_iff`](../../../Math/RepresentationTheory/RestrictedColorWordSupport.lean)
proves, for every binary word of the supplied concrete color kinds,

```
Allowed (Invariants (action word)) ↔ Supports word
```

`Supports` is a positive finite diagram condition. The total vector and
covector degrees must differ by three times a bounded natural number. A
permutation assigns each minority slot to an evaluation pair and groups the
remaining majority slots into triples. Every evaluation pair must connect
distinct leaves; every determinant triple must have three distinct leaf
owners. Repeated copies of a species remain distinct leaves.

There is no unknown Hom, kernel, equivalence, character coefficient, rank
or multiplicity on the right. The theorem has no Weyl, branching,
irreducibility, flag-span or contraction-spanning premise. Its concrete
`Kind` family includes arbitrary symmetric powers and the actual adjoint,
H21, H31 and H22 kernels, opposite actions and actual dual actions. The
arbitrary-tree helper has explicit local symmetry/trace certificates;
`model_certified` and `certified` discharge them for every concrete word.

## Why the necessity proof concerns the whole source

- [`ColorSymmetricTree`](../../../Math/RepresentationTheory/ColorSymmetricTree.lean)
  uses pinned polarization to prove that independent vector/covector pure
  powers determine all linear maps on a symmetric tree. A determinant
  repeating an owner vanishes on the entire symmetric source.
- [`ColorContractionPairFactor`](../../../Math/RepresentationTheory/ColorContractionPairFactor.lean)
  extracts an evaluation pair from either actual canonical contraction.
  The remaining slots occur exactly once, so a normalized fixed pair leaves
  the residual factor unchanged.
- [`ColorTensorFocus`](../../../Math/RepresentationTheory/ColorTensorFocus.lean)
  retains local-to-global slot positions. [`ColorFocusPairTrace`](../../../Math/RepresentationTheory/ColorFocusPairTrace.lean)
  proves that an internal pair factors through the selected leaf's trace.
- [`RestrictedColorCertificates`](../../../Math/RepresentationTheory/RestrictedColorCertificates.lean)
  proves symmetry and trace zero for the actual kernels. Symmetric dual
  swap transports both properties; [`ColorVertexCertificates`](../../../Math/RepresentationTheory/ColorVertexCertificates.lean)
  supplies all opposite/dual certificates.
- [`ColorFocusedSource`](../../../Math/RepresentationTheory/ColorFocusedSource.lean)
  polarizes every other leaf while retaining an arbitrary vector in the
  selected actual kernel. The resulting internal-pair vanishing therefore
  holds on the full actual tensor source.
- [`ColorTreeSupport`](../../../Math/RepresentationTheory/ColorTreeSupport.lean)
  combines these two exclusions with the previously proved raw contraction
  spanning and constructive flag nonvanishing. Every canonical contraction
  survives exactly when its finite owner condition holds.

Flag evaluation proves sufficiency. Necessity separately uses actual
symmetric images and trace kernels, never a supplied flag-span assertion.
No numerical rank/multiplicity computation, raised proof limit, new axiom,
dependency change or external theorem premise is used.

See the [frozen plan](colored-contraction-plan.md),
[previous tree construction](colored-tree-results.md),
[verification](colored-positive-coupling-verification.md) and
[full endpoint plan](colored-support-completion-plan.md).
