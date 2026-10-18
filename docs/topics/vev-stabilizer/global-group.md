# Global group and Hom bridge

## Exact group, cover and kernel

For the specified `diag(2,2,2,-3,-3)` adjoint VEV, the following are proved
group equivalences, not only matching dimensions or Lie algebras:

```
Stab(VEV) ≃ S(U(3) × U(2)) ≃ (SU(3) × SU(2) × Circle) / ker(cover)
ker(cover) ≃ Multiplicative (ZMod 6)
```

- [Generic block equivalence](../../../Math/LieGroups/SpecialUnitary/AdjointBlockEquiv.lean)
  defines `blockPairs I J` with determinant product one. `blockEquiv` extracts
  the canonical blocks; its inverse is `joinBlocks`. It works for arbitrary
  finite block index sets and distinct eigenvalues.
- [Cover](../../../GUT/SU5/Symmetry/AdjointVEVCover.lean) proves `blocks_lift`
  by choosing a sixth root in `Circle`, normalizing the two determinants, and
  verifying the existing integral-hypercharge cover reproduces both blocks.
  This proves `cover_surjective` and `image_eq_stabilizer`.
- `cover_kernel`, `cover_mem_kernel_iff`, `coverKernelCyclicEquiv`,
  `cover_kernel_card`, and `cover_kernel_le_center` reuse the
  [existing kernel classification](../../../GUT/SU5/Embeddings/StandardModelKernel.lean).
  The kernel has exactly six elements and is central, not trivial.
- `quotientStabilizerEquiv` composes the
  [existing quotient-image equivalence](../../../GUT/SU5/Embeddings/StandardModelQuotient.lean)
  with the proved image equality. `quotientStabilizerEquiv_mk` checks its value
  on representatives against the original embedding.
- [Concrete interface](../../../GUT/SU5/Symmetry/AdjointVEVHom.lean) exposes
  `unitaryBlockEquiv`, color/weak evaluation formulas and the explicit inverse
  matrix formula. No choice of sixth root is needed for this block equivalence.

The new equivalences are algebraic. The existing quotient-to-image equivalence
is topological, but this milestone does not assert a new topological block-pair
equivalence or compute homotopy groups.

## Residual Hom and representation descent

[Surjective Hom transport](../../../Math/RepresentationTheory/Decomposition/SurjectiveHomTransport.lean)
proves for any surjective group map `q : G →* K`:

```
Hom_G(a.comp q, b.comp q) ≃ₗ[ℂ] Hom_K(a, b)
```

Both directions preserve the underlying linear map. `nonzero_iff` transports
existence of a nonzero intertwiner. No finite-dimensionality, compactness,
unitarity or continuity of the representations is assumed.

An arbitrary representation `rho` of the covering group need not define a
representation of the actual stabilizer. The exact necessary and sufficient
condition is:

```
(∃ descended, descended.comp cover = rho) ↔ hom.ker ≤ rho.ker
```

`representation_descends_iff` proves this, using the existing
[representation descent construction](../../../Math/RepresentationTheory/Decomposition/RepresentationDescent.lean).
`ambient_representation_descends` proves that restriction of any actual SU(5)
representation automatically descends. `residualHomEquiv`,
`residualHomEquiv_apply`, and `residualHom_nonzero_iff` give the concrete bridge.

Thus an existing algebraic coefficient-to-Hom completeness equivalence can be
composed with this transport when its actual input representations are pullbacks
from the stabilizer, or after proving their kernel conditions. This does not
silently replace the independently supplied flavor/residual group in the four
operator-completeness interfaces by this unbroken gauge group. No new physical
matching or operator classification follows merely from a VEV stabilizer.

## Verification

The persistent [strict audit](../../../GUT/SU5/Audit/AuditAdjointVEVStabilizer.lean)
covers the new constructions and the existing mixing/zero/eigenvalue-collision
controls transitively, permitting only `propext`, `Classical.choice` and
`Quot.sound`. Circle root existence is proved inside Lean; it is not an external
certificate. See the topic overview for final build and commit status.
