# Structural signed and mixed support

This continues the [plan](signed-mixed-plan.md) after the numerical retirement
checkpoint `checkpoint 01`, on the existing topic branch. The statements below
concern the actual statistical original-field coefficient spaces, not exact
multiplicity/rank numerals. No Weyl torus-reduction or new literature premise
is used. Verification is recorded in
[signed/mixed verification](signed-mixed-verification.md).

## Constant Q/L families

For all natural fermion counts n, all natural Higgs counts h,d, any positive
cyclic order k and the existing scalar q/l action, put delta=h-d in integers.
The proved original-Higgs permission criteria are:

| Constant content | Necessary and sufficient conditions |
| --- | --- |
| Positive Q | n*q=0 in ZMod k; n even; n<=24; n+3*delta=0 |
| Conjugate Q | n*q=0 in ZMod k; n even; n<=24; -n+3*delta=0 |
| Positive L | n*l=0 in ZMod k; n even; n<=6; delta=n |
| Conjugate L | n*l=0 in ZMod k; n even; n<=6; delta=-n |

Repeated addition is Lean's `n • q` or `n • l`; this is cyclic charge
neutrality, not an integer equality. Zero fermion degree is included and
reduces to h=d. Companion forbidden theorems negate these exact predicates.
No unevaluated local Hom, kernel, character polynomial or weak-spin
existential remains in these original-Higgs criteria.

The source endpoints are
[SMQuarkAllHiggsSupport](../../../Physics/StandardModel/Operators/SMQuarkAllHiggsSupport.lean)
(`original_ql_iff`, `original_ql_forbidden`),
[SMSignedHiggsSupport](../../../Physics/StandardModel/Operators/SMSignedHiggsSupport.lean)
(`conjugate_quark_ql_iff`, `conjugate_lepton_ql_iff` and forbidden companions),
and the previously checked `SMLowerHiggsSupport.lepton_ql_all_iff`.

Q24 is constructed by transporting a Q12 invariant coefficient through the
perfect complementary exterior pairing, retaining the proved determinant-one
semisimple action. Flipping/currying that coefficient gives a nonzero
constituent map into Q24. The already proved continuous-model Hom symmetry
and exact charge restoration connect it to actual local coefficients.
For all other large Q degrees, original Higgs admissibility, balanced weak
capacity, fermion parity and the hypercharge equation give the exclusion.
There is no basis enumeration of either exterior power or character sum.
The group/source and source/test maps stay symbolic until final application.

Constant conjugate transport is equivariant for the involutive local-group
conjugation, with exact delta sign reversal. It preserves the independent
chirality factors and statistics. Arbitrary residual flavor representations
are evaluated at identity only in the local equivalence; the final full
residual statement is restricted to the existing scalar cyclic q/l family.

## Individual admissible constant-content tests

[SMAdmissibleConstantSupport](../../../Physics/StandardModel/Operators/SMAdmissibleConstantSupport.lean)
closes the actual `QLFiniteSupport.Test` predicates for each of the four
constant families, at every n,h,d,m with the existing proved/checked guard
`BoundedHiggsSupport.Admissible h d m` and delta=h-d. For Q/conjugate Q,
add `m<=min(n,36-n)` to the corresponding row above. For L/conjugate L,
add `m=n`. Thus these are individual constituent tests, not merely an
existence assertion over several weak constituents. Their proof signatures
retain admissibility; no claim is made for arbitrary inadmissible m,delta.

These tests cover the same admissible seed convention used by the original
finite Higgs reduction. They do not prove the retired 107 exact numerical
equalities or re-enumerate a table. The final predicates use only degrees,
parity, capacity and charges; the actual kernel/multiplicity is not evaluated.

## Mixed-content results

[SMMixedConjugation](../../../Physics/StandardModel/Operators/SMMixedConjugation.lean)
proves an actual local coefficient equivalence for every species word p,
with p replaced by its signed opposite and delta replaced by -delta.
`original_ql_iff` proves, for all original Higgs counts and the same cyclic
q,l action,

    Allowed(original(p,h,d)) iff Allowed(original(opposite p,d,h)).

The full residual action is not identified field by field: local transport
is combined with the proved fact that the scalar residual charge changes
sign, preserving its vanishing. The generic
[PatternSpeciesRestriction](../../../Math/RepresentationTheory/PatternSpeciesRestriction.lean)
keeps group/source restrictions abstract before SM specialization, avoiding
large dependent-source rewrites.

[SMChiralitySupport.original_forbidden](../../../Physics/StandardModel/Operators/SMChiralitySupport.lean)
proves for every species word, any supplied residual flavor action and every
Higgs count that an odd number of **either** chirality excludes the entire
actual coefficient space. It also proves local/test vanishing uniformly in
m,delta. The independent left/right action is justified by the previously
proved real-form polynomial comparison; separate independent centers are
not assumed to be elements of the original paired Lorentz group. This is a
necessary test and a complete exclusion of that region, not a sufficient
criterion for the remaining even/even contents.

[SMMixedFamilySupport](../../../Physics/StandardModel/Operators/SMMixedFamilySupport.lean)
connects the existing complete DUQL/QQUE/QQQL/DUUE certificates to the same
`SMFiniteHiggsSupport.OriginalSpace` interface used by the constant families.
`original_ql_iff` and `conjugate_original_ql_iff` classify these four contents
and their four signed conjugates, for all Higgs counts and cyclic q,l:

    Allowed(original(selected content,h,d)) iff h=d and 3*q+l=0.

The forbidden iff is the negation. The underlying positive-family result
already existed; the new theorem is its explicit whole-space bridge to the
shared consumer and its conjugate extension. The proof uses
[MixedSupportSeparation](../../../Math/RepresentationTheory/MixedSupportSeparation.lean)
to prove that simultaneous fermion/scalar content support equals the two
separate support conditions, with all finite multilinear expansions symbolic.
There is no unproved spanning premise or numerical coefficient count.

Finally `factorwise_counterexample` proves that Q3 and L1 each have forbidden
zero-Higgs original spaces at neutral q,l, while their mixed QQQL content
is allowed. Accordingly a test requiring each species factor to have a
singlet cannot classify arbitrary mixed contents. The counterexample concerns
the actual statistical coefficient spaces.

## Remaining general mixed gate

All constant signed Q/L original-Higgs families and their admissible individual
tests are closed in the stated domain. Mixed conjugation, arbitrary-content
chirality exclusions and the eight selected mixed families are closed.
**Arbitrary mixed-content classification remains open.** The exact next
missing interface is a complete full-group branching certificate for the
single-species exterior factors, including their nonsinglet color and spin
components, followed by complete cross-species tensor coupling. The constant
singlet witnesses and the existing tree source decomposition do not supply
that interface. See the [mixed stopping decision](signed-mixed-stop.md).

No full 572-assignment search, universal Delta-B=1 prohibition over all mixed
contents, arbitrary residual symmetry class, generated interaction or rate
is claimed. No numerical multiplicity/rank theorem or new literature premise
was introduced. The statement domain and remaining general mixed gate are
kept distinct from full-project build verification.
