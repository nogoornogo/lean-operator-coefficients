# Symmetric Content Descent Interfaces

[TypedSymmetricPatternHom](../../../../../Math/RepresentationTheory/Symmetric/TypedSymmetricPatternHom.lean)
identifies a fixed-content subspace of the actual full symmetric species
coefficient carrier with invariant typed multilinear maps satisfying all
pattern-preserving permutation relations. Its output may be any supplied
representation, including the algebraic dual of an already statistical
source. The finite species modules and pattern are explicit inputs.

The selected full subspace is defined by vanishing on pure words outside the
pattern orbit. Restriction and stabilizer-normalized reconstruction are
mutually inverse. `sourceSpace_iff` identifies the curried definition with
vanishing for every source vector; no new content correspondence is assumed.

[TwoBlockSymmetricDescent](../../../../../Math/RepresentationTheory/Symmetric/TwoBlockSymmetricDescent.lean)
separately identifies coefficients on a source tensor two symmetric powers
with source-linear, independently symmetric nested forms satisfying actual
simultaneous group invariance. Distinct block module types and arbitrary
degrees are supported. Each quotient descent and both inverse identities
are proved without a finite-dimensional or semisimplicity hypothesis.

The final equivalence joining these two typed presentations is not proved
here. These interfaces do not by themselves transport the earlier weak-singlet
support iff to the original full symmetric direct-sum carrier. Nontrivial
weak-source decomposition likewise requires an actual SU2 carrier certificate.

[HiggsPatternDescent](../../../../../Physics/StandardModel/Operators/Higgs/HiggsPatternDescent.lean)
applies the first interface to the original SM scalar species and arbitrary
exterior degree of its ten signed fermion fields. It retains local, residual
and fermionic statistical constraints and transports allowance/prohibition
predicates. It does not decide whether that typed coefficient space is nonzero.

The [topic result](../../../../topics/sm-support-and-lfv-decomposition/remaining-reduction-results.md)
records the precise remaining join, group-action boundary and verification.

## Completed presentation and full-group transport

[Full Higgs coefficient connection](FULL_HIGGS_COEFFICIENT_CONNECTION.md)
now proves the fixed-content full-field/split equivalence and the actual SM
full-group constituent transport. The earlier isolated result keeps its own
hypotheses; the joint connection supplies the previously missing interface.
Classifying every source Hom support remains separate.
