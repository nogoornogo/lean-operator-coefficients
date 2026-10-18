# LLHH Seed and All-Higgs Support: Connection Completed

## Exact result

For the actual three-generation signed SM/Weyl input with universal physical
cyclic charges (q,q,q,l,l), positive cyclic order k and neutral one-copy
Higgs/dual fields, the whole two-physical-lepton content satisfies

    allowance iff h=a+2 and 2l=0 mod k,
    prohibition iff h!=a+2 or 2l!=0 mod k,
    prohibition at every Higgs count iff 2l!=0 mod k.

The actual LLHH coefficient at (h,a)=(2,0) is constructed and nonzero when
2l=0. Its Higgs-pair dressings are constructed at (h,a)=(r+2,r) for every r.
No zero-Higgs seed is supplied or required, and l=0 is not assumed.
This is not a classification of every L2 fermion content or a mass theorem.

## Physical and statistical bridge

[WeinbergFullSeed](../../../Physics/StandardModel/Operators/WeinbergFullSeed.lean)
starts from the existing actual physical Weinberg one-generation equivalence,
not from a raw LLHH expression or a dimension count. leptonProjection takes
species 3 of the full signed field sum and evaluates its flavor coordinate
zero, retaining the weak/spin/unit-flavor carrier of the source dictionary.
higgsProjection uses the proved actual Higgs/dual representation coordinates.
Both have explicit right inverses, which prove nonzero pullback.

lepton_action and higgs_action prove physical gauge/Lorentz correspondence.
The lepton projection contributes its common cyclic phase, while the Higgs
projection is neutral. phase_two cancels the former when 2l=0. raw therefore
belongs to the actual mixed exterior-two/symmetric-two invariant carrier.
Its fermion values vanish outside LL, and hypercharge fixes two Higgs and
zero dual-Higgs slots. seed is in ContentHiggsSupport.Space rather than only
an ordered field tensor space. The source's fermionic statistics are retained.

## Reusable multiplication and nonzero propagation

[SymmetricCoefficientDressing](../../../Math/RepresentationTheory/SymmetricCoefficientDressing.lean)
constructs multiplication of symmetric-power functionals at degrees p and q.
It combines multilinear maps on disjoint index sets, reindexes to Fin(p+q),
averages over permutations and descends through the actual symmetric quotient.
linear is linear in the first factor. product handles a general representation
X in the first tensor factor and proves covariance for the combined coefficient.

product_apply gives the exact finite permutation sum; product_diagonal gives

    product(f,g)(x tensor b^(p+q)) = f(x tensor b^p) * g(b^q).

A tensor product of symmetric powers is not identified with a higher symmetric
power. Instead, an explicit descended coefficient map is constructed. No
finite generating set or coefficient completeness is inferred from it.

For the LLHH consumer, local_diagonal computes a normalized source value of
one using the physical Weinberg dictionary. boson combines the matching Higgs
vector and an algebraic dual functional in the actual field coordinates.
raw_diagonal and boson_normalized prove both coefficient factors evaluate to
one at this same point for every r. Thus the product is nonzero without a
new nonzero or injectivity premise.

unshifted_fermion_zero transports LL support through every term of the product.
Actual hypercharge and scalar cardinalities then fix (r+2,r). The resulting
dressed coefficient belongs to the whole selected space and is nonzero.
The generic content API supplies necessity; this construction supplies
sufficiency. Its former zero-hypercharge seed constructor is not applied to LL.

## Endpoint and remaining boundaries

The [contract](llhh-contract.md) is complete. The LL shifted-count condition
previously recorded as necessary is now necessary and sufficient in this
whole fixed content at every Higgs count. The shared actual content interface
now has a Higgs-containing seed consumer, alongside the zero-Higgs consumers.
The multiplication construction is reusable for further mixed seeds; their
covariance, support and common nonzero evaluations must still be certified.

Other fermion contents, arbitrary residual actions, finite covariant spanning
and complete all-content support remain open. No VEV evaluation, neutrino
mass, UV completion, anomaly, matching, amplitude or rate is inferred.
The earlier candidate/orbit counts are unchanged. [Verification](verification.md)
records focused/full builds and strict audits. No master merge or push was done.
