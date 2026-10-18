# Actual support without numerical multiplicities

This implements the [bounded plan](non-numerical-support-plan.md) on
`proof/sm-computable-characters`, after `checkpoint 01`. The endpoint is an actual
support classification in the ranges below, not an exact multiplicity/rank
certificate. No Weyl torus-reduction input, new literature premise or
computable character evaluator is used.

## Complete original-Higgs criteria in the proved ranges

Use the fixed three-generation fields, one residual-neutral SM Higgs and its
dual, the existing signed-field convention, independent Weyl factors and
exterior statistics. Let h,d be arbitrary natural Higgs/dual-Higgs counts,
and delta=h-d in integers. Let k be any positive cyclic order and q,l in
ZMod k, acting through the existing scalar q/l flavor representations.

[SMLowerHiggsSupport](../../../Physics/StandardModel/Operators/SMLowerHiggsSupport.lean)
proves these equivalences on `SMFiniteHiggsSupport.OriginalSpace`, the actual
full-field coefficient space with the specified content:

| Content and domain | Necessary and sufficient condition for `Allowed` |
| --- | --- |
| Positive L to any natural power n, including zero | n*l=0 in ZMod k, n even, n<=6, and delta=n |
| Positive Q to power n, with n<=18, including zero | n*q=0 in ZMod k, n even, and n+3*delta=0 |

Here n*l and n*q mean repeated addition (`n • l`, `n • q`). The theorem names
are `lepton_ql_all_iff` and `quark_ql_lower_iff`. The companion
`lepton_ql_all_forbidden` and `quark_ql_lower_forbidden` identify prohibition
with failure of at least one listed condition. No local invariant predicate,
unevaluated multiplicity, matrix kernel test or existential weak-spin test
remains in these final predicates.

For Q, the integer charge equation and parity imply that the nonempty
permitted degrees within n<=18 are precisely 6,12,18; the Higgs differences
are -2,-4,-6 respectively. For L they are 2,4,6, with differences 2,4,6.
At n=0 the criterion reduces to h=d. Arbitrarily many additional H/dual-Higgs
pairs are covered by the iff, rather than sampled at a degree cutoff.

`quark_original_iff` and `lepton_original_iff` also give the hypercharge-only
criteria for the six nonempty degrees with trivial residual group.
`quark_local_iff`, `lepton_local_iff`, `lepton_all_local_iff` and
`quark_lower_local_iff` classify the corresponding existential local Higgs
constituent condition for arbitrary supplied residual flavor actions. These
local statements evaluate the residual action at the identity; they do not
assert invariance under an arbitrary nontrivial residual action.

## Coefficient witnesses, not just constituent embeddings

[SMGenerationCoefficients](../../../Physics/StandardModel/Operators/SMGenerationCoefficients.lean)
proves continuity of the actual semisimple inclusion, weak symmetric-power
self-duality, equivalent continuous source/weak models, and
`restricted_iff`. It identifies actual restricted coefficient permission
with nonzero constituent Hom support. The analytic model carriers and chosen
bases remain symbolic. Their bases, exterior coordinates and action matrices
are not enumerated.

The generic step is
[CompactCoefficientSupport.coefficient_iff](../../../Math/RepresentationTheory/Characters/CompactCoefficientSupport.lean).
It curries the coefficient, uses the supplied self-duality of the test
representation, and reverses Hom support using the proved compact Hom integral
identity. The integral is never evaluated. Continuity, finite dimensionality,
compactness and model equivalences are explicit generic requirements; the SM
consumer constructs/discharges them. No classification or positive
multiplicity premise is substituted for the desired conclusion.

[SMLowerGenerationSupport](../../../Physics/StandardModel/Operators/SMLowerGenerationSupport.lean)
then proves `quark_local`, `lepton_local`, `quark_kernel`, and `lepton_kernel`
for Q degrees 6,12,18 and L degrees 2,4,6, uniformly over every even weak
degree m<=n at the neutral hypercharge. These statements concern actual local
coefficients and actual finite constraint kernels. Local support holds for
arbitrary supplied flavor actions because only their identity action enters.
The vacuum witness uses the existing zero exterior/symmetric equivalences.

## Necessity and sufficiency

Necessity uses the proved scalar hypercharge action. Fermion central parity
excludes odd n. For L, original Higgs admissibility and delta=n force m>=n,
whereas the actual sharp weak bound gives m<=min(n,12-n); together these
exclude n>6, including above-capacity degrees. This exclusion does not depend
on evaluating a finite coefficient sum or a characteristic polynomial.

For sufficiency, choose the minimal admissible weak degree n/3 for each of
Q6,Q12,Q18, and n for L2,L4,L6. The existing generation constructions supply
an injective constituent; compact Hom symmetry and self-duality turn it into
a nonzero coefficient. The proved hypercharge/group factorization restores
U(1), and actual compact/local/kernel equivalences preserve nonvanishing.
The original finite Higgs decomposition restores the full coefficient space.
Finally the existing scalar residual separation proves exactly the cyclic
charge condition, retaining the original residual flavor representations.

## Scope and remaining work

This closes a complete support iff for all constant positive L contents and
for constant positive Q contents through degree 18, with arbitrary original
Higgs counts and arbitrary existing scalar cyclic q/l charges. It is not the
complete Q/L signed family or arbitrary mixed-content classification.
Upper-half positive Q, conjugate Q/L, general residual actions and full
572-assignment/prohibition-pattern certification remain outside this bounded
endpoint. In particular these results alone do not establish universal
Delta-B=1 prohibition over mixed contents.

The local coefficient statements at individual weak degrees are sufficient
permission results; their full arbitrary-m iff is not claimed by the
original-Higgs criteria above. The final predicates classify the original
space, which can contain several admissible weak constituents. No exact
multiplicity/rank numeral, CSV certificate, generated interaction or rate is
claimed. Existing numerical example statements and archived Q18 records are
unchanged. The wider [structural plan](structural-plan.md) remains open.

Persistent audits retain numerical-import rejection and standard-axiom
checks. See [verification](non-numerical-support-verification.md) for focused
proof checks and the outstanding whole-project build boundary.

The later [signed/mixed continuation](signed-mixed-results.md) extends this
checkpoint to all Q degrees, both Q/L signs and individual admissible tests,
with selected mixed consumers. The numerical examples mentioned above were
subsequently [retired](archive/remaining-numerical/README.md) at the user's direction.
