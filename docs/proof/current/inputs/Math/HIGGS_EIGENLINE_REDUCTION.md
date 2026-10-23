# Arbitrary-Degree Coefficient Reduction for Eigenlines

## Statement and actual carriers

[HiggsEigenlineReduction](../../../../../Math/RepresentationTheory/Higgs/HiggsEigenlineReduction.lean)
fixes an arbitrary group G, a complex representation a on X, and a unit-valued
character chi:G->C*. The two scalar representations are the complex lines
with characters chi and chi inverse. Define

    C(h,d) = Hom_G(X tensor (Sym^h C_chi tensor Sym^d C_chi_inverse), C).

These are actual symmetric quotients with independent Higgs and dual degrees,
including degree zero. The source may already be an exterior/statistical
carrier. No finite dimension, semisimplicity, source character decomposition,
coefficient nonzero, seed-existence or spanning premise is required.

There is a constructed linear equivalence

    C(h,d) equivalent to Hom_G(charTwist(chi^h * chi_inverse^d, a), C).

Consequently equal total characters give equivalent entire coefficient spaces.
For every r, C(h+r,d+r) is equivalent to C(h,d). Removing all common pairs
reduces to (h-min(h,d), d-min(h,d)); it preserves both allowance and prohibition.
Balanced support is exactly nonzero invariant source functionals, without a
supplied neutral seed premise.

If a positive k satisfies chi^k=1, then

    C(h,d) equivalent to C(h mod k,d mod k)
           equivalent to C((h + k - (d mod k)) mod k,0).

All-degree prohibition is therefore equivalent to prohibition in the k spaces
C(j,0), 0<=j<k. Existence at some degree is likewise equivalent to existence
in one of these k spaces. A faithful character or minimal period is not required.

## Construction and provenance

The product of scalar coordinates descends through the existing
SymmetricPowerDescent to evaluation:Sym^m C->C. Every pure symmetric tensor is
the product of its coordinates times the tensor of m copies of one. Symmetric
tensors span, so evaluation and z->z*unitTensor are inverse linear maps.
powerEquiv certifies the actual character-power action on this map.

pairEquiv combines the two descended lines. sourceEquiv then absorbs the
resulting character into the source. coefficientEquiv uses the existing
InvariantCoefficientTransport.alongEquiv, which supplies both coefficient
inverse identities. Its downward map evaluates on the two canonical unit
tensors; reconstruction is defined on every coefficient, not just a dressing
range. Cancellation and finite reduction follow from equality of characters.

TauCeti's already pinned CharacterTwist module supplies charTwist and the
tensor-with-line equivalence; its LinearCharacter.Basic supplies actual line
actions. Mathlib supplies multilinear products and group/power arithmetic.
The new symmetric-line descent and all-degree consumers are local proofs.
No general invariant-theory finite-generation theorem is imported or assumed.

alongLines transports certified representation equivalences from other actual
scalar carriers to these lines. A chosen eigenvector, invariant subspace or
embedding into a larger Higgs representation does not meet this premise.

## Controls and boundaries

For a scalar source with character psi, allowance is exactly

    (chi^h * chi_inverse^d) * psi = 1.

This discharges support directly rather than parameterizing seed existence.
The general source still requires the finite Hom tests; finite reduction is
not an automatic algorithm to decompose arbitrary source representations.

The SM Higgs is a weak doublet, not one of these scalar eigenlines. Neutrality
under a residual group does not eliminate its gauge action. In the actual
three-generation input, [HiggsEigenlineBoundary](../../../../../Physics/StandardModel/Operators/Higgs/HiggsEigenlineBoundary.lean)
proves zero-Higgs LL prohibition and LLHH allowance when 2l=0, hence refutes
their support equivalence even with neutral residual Higgs action. This does
not refute reduction to a larger finite primitive set for the weak doublet.

The split symmetric carrier is not newly identified here with a homogeneous
subspace of Sym^(h+d)(B direct-sum D). A consumer using that presentation must
use a proved content/decomposition bridge. The actual SM all-content support
classification, uniform weak-doublet reduction, VEV evaluation and physical
matching remain outside this result.

Verification and the frozen endpoint are recorded in the
[topic](../../../../topics/sm-support-and-lfv-decomposition/higgs-line-reduction-results.md).
