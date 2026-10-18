# Weak-Doublet Higgs Reduction with Weak-Singlet Sources

## Exact all-degree result

[WeakSingletHiggsReduction](../../../../../Math/RepresentationTheory/WeakSingletHiggsReduction.lean)
fixes a group G, an arbitrary complex source representation a on X, a
single complex Higgs doublet b, and a homomorphism j:SU2->G. Its hypotheses
are actual action identities:

- a(j(u))x=x on the whole source;
- b(j(u))v is the defining SU2 doublet action.

The second scalar carrier is the algebraic dual of b, with its contragredient
action. Define the actual split symmetric coefficient space

    C(h,d)=Hom_G(X tensor (Sym^h H tensor Sym^d H-dual), C).

Every coefficient is zero if h!=d. At every natural r, including zero,

    C(r,r) equivalent to Hom_G(X,C),
    C(r,r) equivalent to C(0,0).

Thus allowance iff h=d and Hom_G(X,C) is nonzero, and prohibition iff h!=d
or that source Hom is zero. All-degree prohibition iff prohibition at (0,0).
One source-Hom test suffices for this class; no finite-period assumption is
needed. The source need not be finite-dimensional or semisimple. No seed,
spanning list, finite-generation or source-character decomposition is supplied.

## Actual symmetric dual pairing

[SymmetricDualPairing](../../../../../Math/RepresentationTheory/SymmetricDualPairing.lean)
uses the product of evaluations, independently symmetrizes the vector and
dual slots, and descends through both symmetric quotients. Its coefficient
has diagonal value (phi(v))^r. The general perfectness consumer requires a
finite-dimensional vector space, irreducibility of its r-th symmetric power,
and a certified nonzero phi(v). These inputs are discharged for the doublet.

[WeakDoubletScalars](../../../../../Math/RepresentationTheory/WeakDoubletScalars.lean)
directly reuses the pinned TauCeti.SU2.isIrreducible_symPower proof and its
dimension formula r+1. The constructed nonzero pairing is injective by
irreducibility; equal finite dimensions make it bijective. Currying then
identifies the scalar coefficient space with Hom_SU2(Sym^h H,Sym^d H).
Schur gives zero for different degrees and a scalar multiple of the pairing
for equal degrees. Evaluation on one canonical pair is the inverse scalar
coordinate. This is a full coefficient-space result, not a weight count or
an assumed self-duality of symmetric powers.

## Full source factorization

Fixing any x in the weak-singlet source turns a full coefficient into one of
those weak scalar coefficients. Uniqueness proves

    f(x tensor z) = f(x tensor probe_r) * pairing_r(z).

The downward map evaluates at probe_r. Its invariance under the entire G is
derived from this factorization and the G-invariance of the canonical pairing;
the probe itself is not assumed to be fixed by G. Upward reconstruction is
the tensor product with pairing_r. Both inverse identities are proved.
Color, Lorentz, hypercharge and residual constraints represented in a remain
in the source Hom, as do any already constructed source statistics.

## Actual SM application

[WeakSingletHiggsSupport](../../../../../Physics/StandardModel/Operators/WeakSingletHiggsSupport.lean)
embeds the actual SU2 weak factor into the existing SM covering gauge/Weyl/
residual group and proves that NeutralHiggsPowers.higgs restricts to the
defining doublet. The scalarEquiv consumer gives a one-dimensional scalar
coefficient space at every balanced split degree.

The matter consumer uses the actual uR,dR,eR and their signed dual species
(1,2,4,6,7,9), retaining the existing gauge, Weyl and flavor representations.
Their weak action is proved trivial and transported through arbitrary exterior
degree n. matterEquiv and matterZeroDegreeReduction therefore apply without
a supplied weak-triviality or seed premise. Flavor representations are arbitrary
existing inputs; in particular the preceding three-generation cyclic input
can be supplied. The zero-Higgs source still needs its own coefficient support
classification. It is not replaced by charge neutrality.

## Limits and provenance

The whole source must be weak-trivial, not merely contain a singlet component.
Sources containing nontrivial weak constituents, such as the full LL source,
need additional primitive Higgs cases. Multiple Higgs copies are not identified
with one defining doublet. The split symmetric carrier is not newly equated
here to the selected subspace of a full symmetric direct-sum carrier: that
presentation requires its content bridge. No entire B1/B2/L2 sector or all
ten-species support classification is inferred.

TauCeti's SU2 irreducibility uses actual torus weight vectors and a mixing
group element, not an unproved character-based equivalence. A general
Clebsch-Gordan decomposition, Haar integration and finite covariant-module
generation are not used. No VEV, spectrum, matching or rate result is proved.
The [topic result](../../../../topics/sm-support-and-lfv-decomposition/weak-doublet-reduction-results.md)
records the endpoint and verification.

## Additional group-level input

[Actual SU2 symmetric tensor decomposition](SU2_SYMMETRIC_TENSOR_DECOMPOSITION.md)
now supplies the arbitrary-degree doublet/dual constituents needed for a
future nontrivial-source reduction. Its SU2-only equivalence does not discharge
other SM actions or the original full-field/split connection.

## Completed presentation and full-group transport

[Full Higgs coefficient connection](FULL_HIGGS_COEFFICIENT_CONNECTION.md)
now proves the fixed-content full-field/split equivalence and the actual SM
full-group constituent transport. The earlier isolated result keeps its own
hypotheses; the joint connection supplies the previously missing interface.
Classifying every source Hom support remains separate.
