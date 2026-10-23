# Physics Assumptions: Structural Inputs For Conjugation Routes

[Ledger index](../ASSUMPTIONS.md). These are theorem-specific inputs, not a
universal hypothesis package. Recorded checks retain their topic checkpoints.

## Structural Inputs For Conjugation Routes

The list below describes the conjugation-based routes, not universal premises
of every endpoint. The direct shared-positive, pairwise-positive and automatic entries
retain the source/mass carrier interface and compatible SM action, but replace
conjugation-derived index relations with explicit species-index and positive
support conditions. They do not require actual conjugators or T-unitarity.
This does not remove those hypotheses from the conjugation-based theorems.

1. **Ambient action:** an arbitrary group G, the fixed four-dimensional torus
   `T = SU5.MaximalTorus.Torus`, a homomorphism `j : T -> G`, and an actual
   representation `rho : Representation C (G x H) E` on a finite-dimensional
   complex inner-product space. The product action encodes strict commutation
   of G and H. Merely normalizing G is not enough. This core does not require
   G simple, compact or connected, j injective, a full SU(5) inclusion, or
   continuity of rho as a whole. Continuity is endpoint-specific: the compact
   torus-only endpoint and route A assume continuity of H on E; route B instead
   assumes continuity of the full SM-cover x H action on the radical K.
2. **Actual conjugations:** `TwoConjugations j` supplies ambient elements
   implementing `(3 1)` and `(0 4)` on j(T), with zero-based `Fin 5` indices.
   These are identities for every torus element, not just formal permutations
   of labels. No third representative or relations between representatives
   are inputs. Neither existence for every embedding nor minimality of two
   representatives has been proved. See [the coordinate criterion](../TWO_CONJUGATIONS.md).
3. **Invariant mass:** on `sigma = rho.comp (j.prodMap (MonoidHom.id H))`,
   a complex-bilinear symmetric form B with
   `B(sigma(g)x, sigma(g)y) = B(x,y)` for every g in T x H.
   This is not a Hermitian form or a separately assumed relation `[M,rho]=0`
   for an endomorphism. No mass rank, nonzero mass, Dirac block form, or
   invariance under all of G is required.
4. **Actual light fields:** the light representation is the radical of B,
   not an independently chosen spectrum. Preservation of this radical by
   T x H is **derived**: the mass map `E -> E*` is an intertwiner and its
   kernel is a subrepresentation. The ambient conjugators need not preserve
   B or the radical. Their constraint passes through the conserved dual index.

Definitions: [mass data](../../../../../../Physics/FieldTheory/Mass/Algebra/InvariantMassData.lean),
[radical and dual-index conservation](../../../../../../Physics/FieldTheory/Mass/Spectrum/SymmetricMassIndex.lean),
[residual conjugation transport](../../../../../../Physics/FieldTheory/Mass/Spectrum/ResidualMassIndex.lean).
