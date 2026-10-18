# Species Copy Surplus

## Statements And Scope

[SpeciesCopySurplus](../../../../../Math/RepresentationTheory/Decomposition/SpeciesCopySurplus.lean)
fixes an arbitrary group H and a finite-dimensional complex representation r on
R. For independent representations a,c define `Surplus r a c` by

```
finrank_C Hom_H(R,C) < finrank_C Hom_H(R,A).
```

`exists_nonzero_kernel_map` obtains a nonzero intertwiner R→ker M for every
M:A→C. It uses finite R and C but no irreducibility or source semisimplicity.
`exists_kernel_split` additionally uses irreducible r and semisimple a to obtain
an equivariant split of r in the actual mass kernel. No target semisimplicity,
topology, compactness, continuity, unitarity or finite group is assumed.
Source finite-dimensionality is not needed by these mathematical lemmas;
the physical consumer uses finite species sources and targets.

`family_kernel_splits` applies the same selected r to independent indexed
sources, targets and mass maps. The family index itself need not be finite:
this is a pointwise family result, not an infinite-dimensional mass construction.
Nontriviality of r follows from irreducibility.

## Proof

`postcompose` is the linear map f↦M∘f. `homKernelEquiv` identifies its actual
kernel with Hom_H(R,ker M). The Hom surplus prevents postcomposition from being
injective, producing a nonzero kernel map. Irreducibility makes this map
injective; a subrepresentation of semisimple a remains semisimple, and the
existing retraction theorem splits the injection.

The surplus is a sufficient inlet. Positive total dimension differences do not
imply a shared r across species. Conversely, failure of surplus does not imply
that qque or all light kernels vanish. Hom dimensions are the formal predicate;
no unproved identification with a supplied multiplicity table is used.

## External Gauge Factorization

[ExternalCopyFactorization](../../../../../Math/RepresentationTheory/Decomposition/ExternalCopyFactorization.lean)
proves `exists_copy_map`: for any groups G,H, finite irreducible complex gauge
representation r and finite copy target C, every intertwiner
`external r a → external r c` is id_r tensor a residual intertwiner a→c on
pure tensors. The copy source A may be arbitrary; neither copy action needs to
be semisimple. A finite target basis gives gauge endomorphism slices; Schur's
lemma makes each scalar. A nonzero gauge vector and a dual functional recover
linear copy coordinates, and the full intertwining equation proves their
H-equivariance. Zero-dimensional copy targets are included.

See the [strict audit](../../../../../Math/RepresentationTheory/Decomposition/Audit/AuditSpeciesCopySurplus.lean),
[physical bridge](../../applications/Physics/SPECIES_COPY_SURPLUS_QQUE.md),
and [topic verification](../../../../topics/species-copy-surplus/verification.md).
