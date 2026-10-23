# Physics Inputs And Application Assumptions

This is a navigation index. The linked thematic ledgers retain the complete
statements, hypotheses, derived properties and physical exclusions. Optional
source routes are not universal premises of general completeness.

| Subject | Detailed inputs |
| --- | --- |
| Selected field and symmetry connections | [Dossier](FIELD_CONNECTIONS.md): actual invariant mass/kernel or boundary selection, concrete inverse maps, separate Weyl/dual conventions, invariant tensors and fixed vacua; full stable relations before derivative selection |
| Interacting all-order literature inputs | [Scoped comparisons](../../../../topics/interacting-lagrangian-classification/literature-validation.md) |
| Heeck–Le Existing-Sector Comparison | [Ledger](assumptions/literature-comparison.md) |
| Bounded Derivative Literature Controls | [Ledger](assumptions/derivative-literature.md) |
| Combined Free Weyl/Higgs Current Input | [Dossier](WEYL_HIGGS_CURRENT_INPUT.md) |
| Derivative Input Necessary Parameter Condition | [Ledger](assumptions/derivative-prohibition.md) |
| Li Printed Coordinate Matrices | [Ledger](assumptions/li-coordinate-matrices.md) |
| Reading By Interface | [Ledger](assumptions/reading-guide.md) |
| UV-Generated Yukawa Protection And Exact Radicals | [Ledger](assumptions/mass-protection.md) |
| Structural Inputs For Conjugation Routes | [Ledger](assumptions/conjugation.md) |
| Endpoint-Specific Inputs | [Ledger](assumptions/source-routes.md) |
| Coefficient Classification | [Ledger](assumptions/coefficient-classification.md) |
| Additional Bounded Operator Classifications | [Ledger](assumptions/bounded-sectors.md) |
| Flavor Stabilizer Inputs | [Ledger](assumptions/flavor-stabilizers.md) |
| Derived Properties, Not Extra Assumptions | [Ledger](assumptions/derived-properties.md) |
| What The Conclusions Do And Do Not Say | [Ledger](assumptions/conclusion-meaning.md) |
| Physical Interpretation And Exclusions | [Ledger](assumptions/physical-scope.md) |
| Residual selection criteria | [Ledger](assumptions/residual-selection.md) |
| Bounded Matter/Higgs Completeness Through Seven | [Ledger](assumptions/bnv-seven.md) |
| Graded Completeness: Actual SM Comparison | [Ledger](assumptions/graded-sm.md) |
| Arbitrary-Multiplicity Six-Quark Inverse | [Ledger](assumptions/six-quark-inverse.md) |
| Graded Six-Quark And LLHH Consumers | [Ledger](assumptions/graded-consumers.md) |

See the [cross-domain index](../../../ASSUMPTIONS.md),
[Math ledger](../Math/ASSUMPTIONS.md), [GUT ledger](../GUT/ASSUMPTIONS.md)
and [concrete-model input ledger](assumptions/concrete-model-inputs.md).
No theorem assumptions or proof baseline change with this split.

## Grassmann Weyl Mass Convention

[WeylGrassmannAction](../../../../../Physics/FieldTheory/Mass/Algebra/WeylGrassmannAction.lean)
proves species symmetry of the two-spin Grassmann bracket, its fixed Euclidean
C P_R correspondence, and the symmetric three-species mass-action half.
The kinetic form and the physical/source chirality dictionary are not derived.
Hermitian conjugate terms remain separate. Its strict layer/axiom audit imports
no model sources; the bounded [PS consumer](../../../../topics/ps-bnv-coefficient-bridge/connection-result.md)
does not make this a universal four-component source adapter.

## Chiral Action And Canonical Kinetic Translation

[ChiralActionConvention](../../../../../Physics/FieldTheory/Mass/Spectrum/ChiralActionConvention.lean)
uses a noncommutative star algebra with explicit odd anticommutation, including
formal differentiated components. It proves gamma0 barred reduction, reversed
Hermitian-conjugate order, chiral kinetic matrix translation modulo a formal
divergence, and canonical Majorana factors. Integrating away that divergence
requires an external boundary assumption; no spacetime calculus is proved.
Canonical kinetic forms and the chiral embedding are explicit conventions,
not a theorem about unspecified source metrics. See the bounded
[action consumer](../../../../topics/ps-bnv-coefficient-bridge/action-translation-result.md).

## Neutral Dirac Graph

[NeutralDiracGraph](../../../../../Physics/FieldTheory/Mass/Algebra/NeutralDiracGraph.lean)
uses the shared symmetric Weyl Dirac bilinear, arbitrary complex copy modules
and invertible heavy mixing. Its complete radical and actual coefficient
restriction theorem supply no kinetic normalization, extra Majorana blocks,
model admission or nonzero-generation premise.

## Composable SM and Dipole Prohibition

The [composition results](../../../../topics/composable-prohibition-specifications/results.md)
reuse signed SM fermions with integer 3B/L and the existing two Higgs scalar
species with zero B/L. Scalar flavor actions remain independent supplied
representations. The charge prohibition theorem explicitly requires actual
character actions and detection on each selected content, not only labels.
No mass/light-domain realization or protecting UV model is inferred.

The dipole family reuses its dedicated actual coefficient equivalence, with
finite-dimensional target flavor B inherited from that interface. Each
prescribed vector/dual pair may have a different distinct-weight detector.
These pairs need not form a basis or exhaust LFV. No common-domain identification
with the SM mixed-field input or physical mass-basis construction is supplied.

## Koren SM Finite-Subgroup Selection

[KorenSMSelection](../../../../../Physics/StandardModel/Operators/Selection/KorenSMSelection.lean)
constructs scalar Z9 times Z3 representations on arbitrary complex SM/Higgs
copy modules. Its embedding and restricted-character identity are proved.
With b=3B_usual and l=L, neutrality implies 9 divides b-3l and 3 divides l;
actual all-degree derivative-free coefficients in the union abs(b)=3,
abs(b)=6, abs(l)=2 vanish, as do their residual decomposition factors.
Character-action and detection premises are proved by the construction.

The literature interpretation assumes three colors and three generations;
the algebraic theorem is not an anomaly-freedom theorem for arbitrary modules.
This is a sufficient subgroup certificate for an explicitly symmetry-respecting
input. Full continuous conservation, quantum survival, LFV, UV realization,
masses and rates are not certified. See the
[dossier](../../applications/Physics/KOREN_SM_SELECTION.md) and
[topic](../../../../topics/koren-sm-selection/README.md).

## Flavor Restriction and Quarticity Controls

[DgtFlavorRestriction](../../../../../Physics/StandardModel/Operators/Selection/DgtFlavorRestriction.lean)
constructs the DGT m=1,n=3 Circle flavor dictionary and its actual Z9 SM/Higgs
restriction, including opposite signs and neutral Higgs. Three explicit complex
fermion copies and one Higgs copy are fixed. All-degree B1/B2 prohibition on
the residual input has no undischarged action or detection premise. Separate
B/W dipole selectors use explicit gauge-basis muon/electron/tau vectors; UV
vanishing and residual nonzero witnesses are proved through the existing
actual dipole equivalence. The flavor Hom restriction is not surjective.
No matching, mass-basis or full leptoquark-model admission is supplied.

[QuarticityAdapters](../../../../../Physics/StandardModel/Operators/Selection/QuarticityAdapters.lean)
constructs a gauge-neutral right-Weyl neutrino (Z4/Z2 charges 1/1) and eta
(charges 2/0). Eta's complexified carrier has proved real residual phases.
Bare exterior-square coefficients vanish; the eta-dressed exterior coefficient
is invariant and evaluates to one. Original SM/Higgs-only L2 prohibition is
separate from this extended selected domain. No full-alphabet, anomaly,
vacuum, mass, dark-matter, cosmology or rate claim follows. See the
[dossier](../../applications/Physics/FLAVOR_QUARTICITY_CONTROLS.md) and
[topic](../../../../topics/flavor-quarticity-controls/README.md).

## BGW Z6 SM/Higgs Selection

The [BGW regression](../../applications/Physics/BGW_Z6_SELECTION.md) constructs
scalar Z6 actions on arbitrary complex multiplicity modules of the existing
ten signed SM fermions and two Higgs scalar species. Actual local gauge/Weyl
invariance supplies hypercharge neutrality; no scalar-action or forbidden-space
premise is supplied by the user. The signed integral identity and faithful
character argument derive all-degree absolute Delta B=1,2 prohibition.
No dimension/semisimplicity or generation-count premise is needed algebraically.
Anomaly freedom and UV origin are not proved. The charged-Higgs LLHH follow-up
constructs a nonzero coefficient for one complex lepton/Higgs copy through a
proved whole-domain equivalence and the existing Weinberg coefficient theorem.
It assumes no VEV or generated mass/coefficient; individual charged and neutral
Higgs actions are not equated.

## Input-Side SM Prohibition Facade

The [input-side results](../../../../topics/prohibition-input-api/results.md)
reuse ComposableBLSupport's actual SM/Higgs domains. The LLHH necessity iff
uses one complex lepton flavor copy, neutral Higgs flavor and the proved
WeinbergSMInterface coefficient equivalence. Its detected scalar is the square
of the lepton action. Koren/BGW, DGT and quarticity consumers reuse existing
certificates with their original field alphabets and hypotheses; no extra
model-wide necessity or classification is asserted.

## Representative Target Connections

The [twelve-row catalogue](../../../../topics/prohibition-patterns/catalogue.md)
uses `Physics.ProhibitionPatterns` to select any subset of absolute B1/B2/L2 on
one existing SM/Higgs input. Joint prohibition is a conjunction with prescribed
dipole selectors on their separate admitted coefficient domain; it neither
asserts a universal LFV sector nor identifies LFV with total L. The DGT joint
example uses the same UV Circle residual group; UV baryon prohibition follows
from the existing Z9 restriction identities and the unchanged underlying
coefficient map. Koren and BGW remain sufficient examples, not necessity
classifications or nonzero-admission premises.

## Mixed BGW and Selected-LFV Consumers

`Physics.MixedSelectionPatterns.bgw_satisfies` combines B1/B2 all-degree selected
coefficient prohibition with fixed-(2,2) charged-Higgs LLHH allowance on the
existing BGW one-copy SM/Higgs actions. Allowance uses the certified actual
coefficient equivalence and witness. DGT allowance is the nonzero output of
specified IR dipole selectors, separate from UV prohibition. See the
[mixed results](../../../../topics/mixed-selection-patterns/results.md).
No new literature premise, field admission, matching or generation is inferred.

## DGT and Quarticity Mixed Requests

The [two-model consumers](../../../../topics/dgt-quarticity-mixed-requests/results.md)
reuse the fixed DGT m=1,n=3 Z9 IR dictionary for both all-degree SM/Higgs B1/B2
prohibition and allowance of each prescribed IR dipole selector image. The
corresponding UV Circle selector images are forbidden. Quarticity uses its
original Z4 times Z2 action: SM/Higgs-only L2 and selected bare nuR coefficients
are forbidden while the selected eta-dressed domain is allowed. Field domains
remain distinct; no full extended-alphabet, mass-basis LFV or generated
interaction claim is supplied. No generic API hypothesis or literature premise
is added by packaging these proved statements into requests.

## Selected Non-SUSY Mixed Consumers

The [dossier](../../applications/Physics/NON_SUSY_MIXED_CANDIDATES.md) records
explicit Dev–Mohapatra SM/Higgs parity, one-copy LLHH, and two-flavor local
six-quark domains, plus Ma et al. selected singlet N/complex chi2 actions.
The actions, prohibition and nonzero witnesses are proved. Source dictionaries
are restricted interpretations: no full alphabet, generated matching,
antisymmetric printed channel, full flavored SM six-quark transport, anomaly,
vacuum, mass or rate claim is supplied by these original consumers. The
selected Dev connection below supplies its separate action/contraction results.

## Species-Surplus Necessary Constraints

[Constraint register](../../../../topics/theorem-driven-protection-constraints/constraints.md):
`Physics.SpeciesSurplusNecessity.bottleneck` requires the original invariant mass,
an actual species Realization, semisimple source representations and a finite
common irreducible. Vanishing of the participating physical exterior space
forces at least one species' source Hom multiplicity not to exceed its target.
`count_bottleneck` additionally requires six actual Hom-count equalities.
These are necessary conditions only. An all-B1 consumer must prove the
selected-domain implication; total copy dimensions and UV characters are
not automatically valid count/radical dictionaries.

## Abelian Residual Qque Prefilter

[Residual filter](../../../../topics/theorem-driven-protection-constraints/residual-prefilter-results.md):
`Physics.ResidualQquePrefilter` requires a genuine SM x Abelian-H action and
actual invariant Q/uc/ec subspaces with full character-twisted equivariant
identifications. It transports dual uc/ec to right-handed carriers and
excludes prohibition covering every admitted triplet when one qque character
is trivial. This uses existing neutral exterior evidence. It requires no
semisimplicity or compactness, but gives no converse, UV realization or
full B1 domain certificate. Finite filtering separately requires decidable
predicates; a missing subspace dictionary is unknown coverage.

## Constructed Inverse Cyclic SM Input

[Proof dossier](../../applications/Physics/INVERSE_CYCLIC_SM_CONSTRUCTION.md):
`Physics.InverseCyclicSMYukawa.construction_certificate` constructs three-generation
SM x Z2 lepton-parity fields, a charged singlet/dual spectator evaluation mass
with exactly the declared SM radical, nonzero physical Yukawa exterior
coefficients in three channels and all-degree B1 prohibition on the declared
signed fermion/Higgs alphabet. The finite charge filter fixes neutral Higgs,
universal charges and 2<=k<=12; counts are labeled charge tuples, not models.
The new construction supplies actual gauge/copy/spin and flavor-dual bridges;
no radical, nonzero coefficient or nondegeneracy premise is assumed.
The imposed symmetry is not certified anomaly-free or quantum exact. No
simple-group lift, dynamical VEV, realistic masses/mixing, matching or rate
claim is supplied. Passing the arithmetic filter is not a protection theorem.

The [bounded converse](../../../../topics/inverse-cyclic-sm-construction/bounded-converse-results.md)
now makes that filter exact for the actual three-generation universal-charge
dimension-six DeltaL=1 four-family sector: prohibition iff 3q+l != 0, and
allowance iff equality to zero. This adds no hypotheses and covers all positive
cyclic orders symbolically. It does not change the all-degree or UV boundaries.

### Bounded inverse-charge follow-ups

Finite diagonal cyclic flavor modules and normalized basis/projection selectors
give selected dipole allowance iff selected charges agree. Arbitrary LFV
selectors are excluded. Universal physical q/l charges and neutral Higgs give
one-copy B2/LLHH prohibition iff 6q/2l is nonzero; the original domains remain
fixed. Fixed-order common unit scaling preserves these tests, with 151 finite
orbits and certified actual phase-image cardinalities. No cross-order model
equivalence, quantum validity or all-degree converse is inferred. See the
[bounded result](../../../../topics/inverse-cyclic-sm-construction/three-followups-results.md).

## Bounded Converse Extensions and Controls

[Results](../../../../topics/prohibition-converse-boundaries/results.md):
CyclicSelectorDipoleSelection permits arbitrary vectors/functionals on finite
diagonal cyclic modules; allowance iff a matching-charge coordinate pair has
nonzero selector support. Zero selectors are included. Nonabelian weight-only
classification and generated-coefficient surjectivity are not supplied.

BalancedSpeciesSurplusControl constructs actual species mass squares and
light ranges for equal source/target finite nontrivial residual actions with
zero invariant mass. There is no surplus for any tested r, yet a physical
exterior coefficient exists. Thus lack of joint surplus is not a prohibition
criterion; no exact SM radical or nondegenerate-mass counterexample is claimed.

AdmittedCyclicSMProhibition transports the support-guarded all-degree charge
iff to the signed SM/Higgs facade. Odd-fermion zero coefficients and neutral
triple-Q lepton-parity content refute necessity of raw-content detection.
Actual even-degree carrier support remains to be classified. This does not
certify all-degree protection for the 572 assignments or 151 generator orbits.

## S3, Decomposition-Based LFV and DUQL Higgs Powers

[Results](../../../../topics/sm-support-and-lfv-decomposition/results.md):
S3DipoleSelection uses the exact C^3 permutation action; its centralizer and
actual B/W selector iff are proved. SemisimpleDipoleSelection requires certified
actual equivalences to finite irreducible block products and keeps selector
matrix-unit evaluations. Scalar cyclic modules give a checked consumer;
nonabelian decomposition discovery and generated LFV rates are not inferred.

DressedDuqlFamily fixes three universal cyclic generations and neutral one-copy
Higgs/dual fields. Actual DUQL-only coordinates and normalized symmetric-power
pairings give allowance iff 3q+l=0 for every dressing power r. This is a family
range at degrees (4,2r), not all contents. ThreeGenerationFermionBound proves
the signed full-field dimension 180 and exterior/coefficient vanishing above
it, with a finite count superset only. No scalar cutoff or complete support
classification is claimed; uniform covariant spanning remains the stop boundary.

## Whole-content DUQL Higgs support

[Result](../../../../topics/sm-support-and-lfv-decomposition/duql-content-results.md):
DuqlHiggsContent fixes actual three-generation universal cyclic fermions,
one neutral Higgs/dual copy and one each of DUQL. Every positive cyclic
order and every scalar count h,a have allowance iff h=a and 3q+l=0.
The content is defined independently of seeds, and witnesses use the
existing actual dictionary and pairing powers. No VEV, mass, finite
generation or semisimplicity premise is added. The result does not
assert coefficient spanning, UV realization or full all-content protection.

## Four-family all-Higgs support

[Result](../../../../topics/sm-support-and-lfv-decomposition/four-family-results.md):
FourFamilyHiggsContent fixes the same actual three-generation universal
cyclic and neutral Higgs input. Each DUQL/QQUE/QQQL/DUUE whole-content space
has allowance iff h=a and 3q+l=0, for every positive k and arbitrary h,a.
Actual statistical coordinate equivalences supply the witnesses; no
spanning, semisimplicity or nonzero premise is added. The four-content
union has the same support criterion and all-Higgs prohibition iff
3q+l!=0. This is not a criterion for every all-degree B1 content.

## Generic content seed adapter

[Result](../../../../topics/sm-support-and-lfv-decomposition/content-adapter-results.md):
ContentHiggsSupport fixes the actual universal cyclic three-generation and
neutral Higgs input, accepting arbitrary fermion content/degree and proofs
of its constant hypercharge Y and residual charge c. Necessary count/charge
conditions need no seed premise. For Y=0, neutral supported exterior seed
existence is explicit; nonzero balanced propagation and the support iff
are derived. The four-family consumers discharge seed existence. LL shifted
counts are necessary only; arbitrary support and finite generation remain
unproved. Parity, degree and indivisible-hypercharge exclusions are actual
zero-coefficient results. No UV or quantum validity follows.

## Outside-family adapter trials

[Result](../../../../topics/sm-support-and-lfv-decomposition/outside-family-results.md):
Under the same actual universal cyclic and neutral scalar input, a constructed
empty-degree invariant seed certifies pure-scalar allowance iff h=a. Triple Q
is forbidden even when its numerical filters hold. SixQuark uR²dR⁴ necessity
uses actual species labels and requires h=a and 6q=0. six_iff_of_seed keeps
actual neutral supported exterior-six seed existence explicit and unproved.
Separate typed six-quark tensors are not assumed to inhabit this carrier.

## Actual six-quark seed connection

[Result](../../../../topics/sm-support-and-lfv-decomposition/six-seed-results.md):
SixQuarkFullSeed discharges the previously explicit six-quark seed premise
using an actual statistical local coefficient, full-field projection with
a right inverse, and gauge/Lorentz/cyclic covariance. Under the same
three-generation universal cyclic and neutral scalar input, uR²dR⁴ has
whole-content allowance iff h=a and 6q=0 at every positive cyclic order.
No q=0, seed existence, semisimplicity or literature premise is added.
This supersedes the earlier unproved seed boundary for this content only;
other contents, finite spanning and complete B2 support remain open.

## Actual LLHH Higgs-containing seed

[Result](../../../../topics/sm-support-and-lfv-decomposition/llhh-results.md):
WeinbergFullSeed uses the same actual three-generation universal cyclic and
neutral Higgs/dual input. The physical/statistical Weinberg dictionary and
proved field right inverses give an LLHH seed when 2l=0, without assuming
l=0 or seed existence. Symmetric coefficient multiplication, a common
nonzero evaluation and actual support transport give whole-content
allowance iff h=a+2 and 2l=0 at arbitrary Higgs counts. This closes the
previous shifted LL sufficient-direction gap. No VEV, neutrino mass,
finite covariant generation or full L2 classification follows.

## Boundary of eigenline Higgs reduction

[Result](../../../../topics/sm-support-and-lfv-decomposition/higgs-line-reduction-results.md):
HiggsEigenlineBoundary uses the unchanged actual three-generation universal
cyclic charges and neutral residual Higgs action. LL at zero Higgs is forbidden;
LLHH is allowed when 2l=0. Their allowance predicates therefore cannot be
identified from residual neutrality. This is a counterexample to zero-Higgs
reduction, not to all finite weak-doublet reduction. No additional physics
premise or classified SM content is introduced by the eigenline Math result.

## Actual SM weak-singlet Higgs reduction

[Result](../../../../topics/sm-support-and-lfv-decomposition/weak-doublet-reduction-results.md):
WeakSingletHiggsSupport constructs the actual weak inclusion and proves the
existing single neutral-multiplicity Higgs action restricts to the defining
SU2 doublet. The source uR,dR,eR and signed dual fields retain their actual
color, Weyl and arbitrary supplied flavor representations. Weak triviality
of their field sum and every exterior power is derived, not an extra matter
premise. Balanced split Higgs coefficients are equivalent to zero-Higgs
source coefficients; unbalanced degrees vanish. The zero-Higgs source support
and its fixed-content/direct-sum bridge remain separate. No full ten-species
classification, VEV, mass, anomaly, matching or rate result is inferred.

## Fixed-content symmetric descent

[Result](../../../../topics/sm-support-and-lfv-decomposition/remaining-reduction-results.md):
HiggsPatternDescent supplies actual ten signed SM field actions, an
arbitrary exterior degree and supplied flavor representations, with the
existing neutral scalar multiplicities. No weak-singlet premise is required
for its full-field/typed-pattern coefficient equivalence.
No seed, source semisimplicity or nonzero premise is added. The equivalence
between typed pattern compatibility and the split nested symmetric space
remains open, as does nontrivial-source SU2 finite support reduction. These
proved descent interfaces are not a complete support classification.

## Original SM full Higgs coefficient connection

[Result](../../../../topics/sm-support-and-lfv-decomposition/full-higgs-connection-results.md):
SMHiggsConstituents proves actual weak and hypercharge projections and the
full-group Higgs constituent equivalence. FullHiggsCoefficientBridge uses
the original one-Higgs/dual species with neutral scalar multiplicities C,
an arbitrary actual source and natural scalar counts h,d. Its full-field
space is proved to mean exactly the selected scalar counts. Both split and
constituent coefficient equivalences preserve color, Weyl, hypercharge,
residual and source statistical constraints. The actual signed-field exterior
source with supplied flavor actions is a proved consumer. The weak-singlet
corollary retains its explicit whole-source weak-triviality condition.
All-source invariant Hom support, multiple Higgs copies, other residual Higgs
actions, quantum validity, UV realization and rates are not established.

## Mixed Cyclic Qque Pair Filter

[Bounded extraction](../../../../topics/sm-support-and-lfv-decomposition/su6-necessary-condition-results.md):
`Physics.MixedQqueCyclicNecessity` uses finite diagonal cyclic flavor actions at
positive cyclic order and the existing physical exterior completeness
dictionary. Prohibition forces every mixed pair charge q(i)+q(j)+u(a)+e(b)
to be nonzero. The three-generation control passes diagonal tests but has a
nonzero mixed coefficient in the actual signed sector. No Yukawa, mass, UV
lift or full all-degree prohibition is asserted.

## Common Non-Abelian Flavor Qque Samples

[Sample results](../../../../topics/sm-support-and-lfv-decomposition/outside-class-sample-results.md):
`NonabelianQqueSamples.common_flavor_left_species` uses any nontrivial finite
complex flavor representation shared by Q/uc/ec. Actual dual tensor transport
connects left-handed uc/ec to right-handed coefficient fields; the existing
matched split theorem supplies a nonzero physical fermionic exterior
coefficient. No Abelian, scalar, irreducible or invariant-line premise is
required. S3 permutation and A4 standard samples have genuinely noncommuting
represented generators; A4 has no invariant flavor functional yet allows qque.
These species are not asserted to be a UV mass radical. No full B1 prohibition,
Yukawa compatibility, quantum symmetry or rate result is inferred.

## Unequal S3 Qque Tensor Samples

[Sample results](../../../../topics/sm-support-and-lfv-decomposition/sm-preserving-sample-results.md):
`S3QqueTensorSamples` uses actual three-dimensional S3 permutation, trivial-copy
and sign-copy flavor actions on the physical right-handed coefficient inputs.
The independent flavor actions commute with the actual SM gauge factor.
Physical qque is forbidden for (permutation,trivial,sign) and allowed for
(permutation,sign,sign). Q and sign have no common irreducible; semisimplicity
is derived from finite S3 over C. The negative result uses Q-pair statistics.
No shared uniform multiplicity dictionary exists for the chosen Q/u actions;
invariant Q-to-u maps are noninjective or zero. Applying that gate to physical
neutral-Higgs Yukawa masses requires the flavor-map correspondence. No full
B1 prohibition, UV lift, radical/VEV or complete Yukawa certificate is asserted.

## S3 sample with bijective flavor-map gates

[Result](../../../../topics/s3-yukawa-compatible-qque/results.md):
`S3YukawaCompatibleQque` fixes physical Q,uR,dR to the three-dimensional S3
permutation action and L,eR to three sign copies, with residual-neutral Higgs.
Independent gauge/flavor product actions commute; the actual quark actions
are noncommuting. Identity intertwiners give bijective Q→uR, Q→dR and L→eR
flavor maps. An explicit nonzero Q-symmetric invariant coefficient and the
existing physical exterior equivalence prove selected qque allowance for the
same dictionary. No external mathematics or literature premise is added.
Physical Yukawa matching, realistic masses/mixing, UV/anomaly realization,
full B1 classification and the full signed-field bridge are not established.

## Finite SM/Higgs support table with residual parameters

[Dossier](../../applications/Physics/SM_FINITE_HIGGS_SUPPORT.md):
SMFiniteHiggsSupport uses the actual ten signed SM fields, the fixed flavor
carriers Fin 3 -> C with supplied representations of a group H, and one
neutral-residual Higgs doublet/dual with hypercharges +3/-3. No relation
between the independently supplied signed flavor representations is silently
imposed. Gauge/Weyl/residual actions and exterior statistics remain explicit.
The weak-weight bound, fixed-content source and original-carrier transport
are constructed. All Higgs degrees reduce to finitely many actual full-group
invariant Hom predicates. The degree-180 exterior vanishing theorem bounds
the full fermion universe. No seed positivity, source semisimplicity,
finite-generator certificate or classification of Allowed(T) is assumed.
Classifying these predicates for q/l actions or new residual classes,
additional Higgs inputs, derivatives, UV/quantum realization and rates remain
outside this endpoint.

## Existing q/l residual separation

[Checkpoint](../../../../topics/sm-ql-support-classification/results.md):
QLFiniteSupport instantiates the preceding finite table with the existing
three-generation cyclic q/l flavor dictionary at positive order k. Signed
species charges are [q,q,q,l,l,-q,-q,-q,-l,-l] and Higgs is residual neutral.
The scalar residual action on the actual statistical source and Higgs
constituent is proved. At this checkpoint, full support was equivalent to
total residual charge zero and the remaining actual local gauge/Weyl Hom
support; the complete finite classifier appears below.

## Actual Weyl generator and kernel controls

[Checkpoint](../../../../topics/sm-local-invariant-kernel/results.md):
WeylGeneratorTests uses actual SL(2,C), preserving any supplied paired
left/conjugate-right representation. Actual transvection generation is
proved, but those parameters still range over C. WeylFiniteKernelControl
discharges a finite two-element test and full coefficient/kernel equivalence
for one actual left Weyl spinor, with zero kernel. This checkpoint alone does
not certify finite tests or polynomial descent for all statistical SM contents;
the later sections discharge those obligations.

## Actual all-content statistical Weyl kernels

[Actual statistical-kernel result](../../../../topics/sm-statistical-finite-kernel/results.md)
certifies four real/imaginary transvection families for actual paired Weyl
SL(2,C), affine actions for all signed three-generation fields, degree at most
n through the actual content image, and 4(n+1) exhaustive labelled tests on
source tensor Higgs constituent. Residual flavor actions remain arbitrary
and are evaluated at identity for this Weyl restriction. Higgs is Weyl-fixed.
`SMWeylFiniteKernel.coefficientEquiv` / `canonicalEquiv` have no supplied
exhaustiveness/degree premise; the optional basis is classical finite carrier
data. Its rank criterion is Weyl-only. `SMQLPartialKernel.original_allowed_iff`
connects original q/l coefficients to this kernel **with actual gauge
conditions retained**, preserving q/l neutrality and bounded Higgs indices.
At this checkpoint compact finite sampling and the full local rank predicate
were still unproved. Strict persistent audit: `AuditSMStatisticalFiniteKernel`.

## Complete actual-local finite kernels for the fixed SM input

[Compact finite-kernel result](../../../../topics/sm-compact-kernel-completion/results.md)
constructs integral color weights for all ten signed species and descends them
through the actual statistical source. Existing weak weights, exact Higgs
symmetric-power weights and hypercharge weight `3*delta` supply the other
compact factors. Six color, two weak, one hypercharge and `4(n+1)` paired-Weyl
tests are proved exhaustive on every length-n content source tensor Higgs
constituent. `SMFullLocalKernel.coefficientEquiv` and
`allowed_iff_rank_lt` have no supplied exhaustiveness or polynomiality premise.
`SMQLFullKernel.original_allowed_iff` composes this with q/l charge separation
and the all-degree Higgs reduction, leaving a finite matrix-rank predicate and
no invariant-Hom `Allowed` term. All-content exact ranks and the rank-based
all-degree classification of the 572 assignments are not computed. The bounded
recount and fixed LLHH rank below are subsequent results. Persistent strict
audit: `AuditSMCompactFiniteKernel`.

## Charged local matrix rank and bounded recount

[Rank evaluation record](../../../../topics/sm-rank-enumeration/results.md):
`SMChargedKernelRank.full_rank` proves full column rank of the same actual
local matrix whenever `hypercharge(p)+3*delta != 0`. Above fermion degree 180,
the carrier and constraint rank are zero. No computational basis is assumed
or supplied. General neutral ranks within the degree cutoff remain unevaluated. The
external 572-assignment CSV reproduces existing bounded predicates and is not
an all-degree protection result or a Lean premise. Strict persistent audit:
`AuditSMChargedKernelRank`.

## Fixed LLHH statistical kernel rank

[LLHH rank certificate](../../../../topics/llhh-kernel-rank/results.md):
`LLHHKernelRank` constructs the connection from constant lepton content to
the existing Weinberg exterior model. For three flavors, `m=2`, `delta=2`,
and trivial residual group, the actual local carrier has dimension 198,
kernel dimension 6 and rank 192. Explicit exterior/tensor coordinates preserve
the original rank. `residualEquiv` retains arbitrary supplied residual flavor
representations as `Hom_H(Sym²(flavor 3), C)`; their invariant dimension is not
asserted to be six. Literature is guidance, not a theorem premise. There is
no executable complex-elimination backend or all-content rank classification.
Persistent strict audits: `AuditConstantPatternExterior`, `AuditLLHHKernelRank`.

## Exact rank certificates and content multiplicities

[Certificate and compression result](../../../../topics/sm-rank-certificates/results.md):
`SMRankMultiplicity.rank_eq` proves that equal species counts imply equal
actual local ranks, for arbitrary supplied flavor representations, m and delta.
`SMExactRankBridge.rank_from_certificate` consumes an explicit coefficient/kernel
equivalence and an exact rational rank certificate; it does not construct
that equivalence for all contents. The external rational Gaussian elimination
generator emits identities checked by the Lean kernel. Its computations are
not theorem premises. No rationality assumption is imposed on the original
complex matrices. All-content invariant multiplicities remain unclassified.
Persistent audits: `AuditExactRankCertificates`, `AuditSMRankCertificates`.

## Numerical constant-content ranks and odd-degree obstruction

[Numerical rank table](../../../../topics/sm-rank-certificates/constant-results.md):
`SMConstantContentRanks.carrier_dimension` proves
`choose(species dimension,n)*(m+1)` for every constant species word.
`charged_rank` and `above_capacity_rank` prove full rank under hypercharge
mismatch and zero rank above species capacity. `SMParityKernelRank.full_rank`
proves full rank for all odd-length words using the actual central Weyl action.
These structural formulas allow arbitrary residual flavor input. The executable
`evaluate` specializes to trivial residual input; `evaluate_sound` proves
soundness of every returned rank. Its exported partial table has 19161 known
ranks and 107 unclassified neutral entries among 19268 constant-content
candidates. Of the known ranks, 19160 are structural full-rank cases
(odd fermion degree or hypercharge mismatch). Among the 108 even-degree
hypercharge-neutral entries, only LLHH is numerically certified: 1 of 108.
Mixed contents and residual selection are not classified by that table.
Persistent audit: `AuditSMNumericalRanks`.

## Structural constant-source characters

[Structural character milestone](../../../../topics/sm-rank-certificates/structural-character-results.md):
`SMConstantSourceCharacter.weak_character` computes the actual constant-species
source character at the weak torus for arbitrary degree and supplied residual
flavor actions. `lepton_character_product` retains independent weak and left
Weyl torus variables and proves the four-factor exterior generating formula
with three flavor copies. The residual element is the identity; this is not
a classification for arbitrary residual selection. `SMLCompactWeyl` now proves
compact-to-actual SL(2,C) invariance for the L statistical source and its Higgs
constituents, for arbitrary degrees. `compactKernelEquiv` identifies compact
local invariant coefficients with the actual finite constraint kernel. This
is local invariance, not classification of the supplied residual action; mixed
chirality is not covered. The subsequent L/conjugate-L character-integration
adapter and local support criterion are now proved, as recorded below. No new
CSV values are certified.
Persistent audits: `AuditSMSourceCharacter`, `AuditSMLCompactWeyl`.


## Uniform L/conjugate-L local multiplicities

[Uniform lepton result](../../../../topics/sm-rank-certificates/lepton-multiplicity-results.md):
`SMLKernelDimension.kernel_dimension` identifies the actual neutral L finite
kernel dimension with a finite sum of signed weak/Weyl weights, uniformly in
fermion/Higgs degrees. `allowed_iff` proves local support iff delta=n and this
multiplicity is nonzero. The source has three flavors and exterior statistics;
`SMLContinuousCharacter` proves the required analytic-copy continuity rather
than supplying it as a hypothesis. `SMLConjugateMultiplicity` transports the
entire local coefficient space with delta reversed; conjugate-L support is
delta=-n and the same multiplicity nonzero. Supplied residual flavor actions
remain independent inputs, and their identity restriction is used for local
counting. Residual invariance, mixed contents and Q/color A2 extraction are
not classified. No new literature premise or physical matching assumption is
added. Persistent audit: `AuditSMLMultiplicity`.


## Constant Q/conjugate-Q exact local support

[Q/conjugate-Q result](../../../../topics/sm-rank-certificates/q-gaussian-results.md):
`SMQGaussianKernel.matrix_semantics` identifies the explicit Gaussian-rational
finite family with the actual Q statistical-source/Higgs constraints in an
explicit exterior/monomial basis. The field entries, all group samples and
induced exterior/symmetric coordinates are proved; no rationality or rank
certificate is left as an input. `kernel_dimension` and `rank_add_nullity`
give the original local finite kernel dimension and rank from the symbolic
Gram characteristic polynomial. `allowed_iff` is its exact zero constant-
coefficient predicate. `SMQConjugateKernel` proves whole coefficient-space
transport, reversing delta, and the corresponding dimension/support/rank
formulas. Degrees are arbitrary and flavor count is three. Residual group
actions remain supplied, with their identity restriction used for local
counting; mixed species and residual selection are not classified. The full
coordinate construction is a Route B variant; zero-weight compression and
efficient large-degree numerical evaluation are not asserted. No CSV rows
were newly certified. `SMConstantFullSupport` additionally connects the four
constant Q/L families to the original unreduced Higgs coefficient space at
arbitrary h,d, with the residual group explicitly fixed to Unit and the
existing trivial three-flavor action. Its criterion is the bounded constituent
existence test plus the proved weight/polynomial predicate. Persistent audit:
`AuditSMQGaussianKernel`.


## Two-species SM source dimensions

[Binary mixed-source result](../../../../topics/sm-rank-certificates/mixed-mathlib-results.md):
`SMBinaryContentRanks.sourceEquiv` preserves the actual gauge, paired Weyl and
supplied residual action for any distinct signed SM species pair. Three flavors
and arbitrary exterior/Higgs constituent degrees are retained. Exact source
and carrier dimensions, hypercharge, original local rank-nullity and charged/
odd full-rank tests follow without computed matrix entries. Equal-multiplicity
orderings share the proved source dimension. Neutral invariant multiplicities,
three-or-more-species contents and residual selection remain unclassified;
no table entry or A2 counting premise is introduced. Persistent audit:
`AuditSMBinaryContentRanks`.


## Arbitrary-content mixed-chirality compact comparison

[Mixed-chirality result](../../../../topics/sm-rank-certificates/mixed-chirality-results.md):
`SMMixedCompactWeyl.coefficient_fixed_iff` compares the actual paired
left/entrywise-conjugate-right Weyl action with independent compact SU2 factors,
for every signed content and source/Higgs constituent. Actual affine actions,
polynomial source descent, transvection generation and factor spanning are
proved; no density, polynomiality or decomposition premise is left supplied.
`SMMixedCompactCoefficients.fullEquiv` retains arbitrary gauge/residual action
conditions verbatim, and `localEquiv`/`kernelEquiv` connect the local compact
constraint space to the existing actual finite kernel. `original_allowed_iff`
retains full-field statistics and arbitrary Higgs degrees through the proved
finite constituent reduction. Three-generation multiplicities remain fixed.
The compact coefficient spaces are simultaneous invariant submodules; a new
combined product representation, its continuity/Haar character counting, A2
extraction and residual classification are not asserted. No CSV values or
physical matching inputs change. Persistent audit: `AuditSMMixedCompactWeyl`.


## All-content ten signed species source decomposition

[Iterated mixed-source result](../../../../topics/sm-rank-certificates/iterated-mixed-results.md):
`SMIteratedContent.sourceEquiv` instantiates the constructed finite dictionary
at the existing ten signed field representations, with one exterior leaf per
species and its degree equal to the word's occurrence count. The label
bijection, equivariant field identifications and word length are proved.
All ordered contents, including the empty word, retain the full gauge, paired
Weyl and supplied residual flavor action. Three-generation carriers are fixed.
`source_dimension` is the product of the ten binomial dimensions;
`carrier_dimension` multiplies it by `m+1` for the actual Higgs constituent
matrix carrier. Source characters multiply, and spectator/supported full-group
coefficient equivalences are proved. Actual local rank-nullity, charged and
odd full-rank consumers use this symbolic column count without enumerated
matrix entries. Neutral invariant multiplicities and residual classification
remain open; no new CSV values, literature premises or numerical zero tests
are used. Persistent audit: `AuditSMIteratedContent`.


## Conditional Weyl extraction to actual SM kernels

[Conditional extraction result](../../../../topics/sm-rank-certificates/weyl-input-results.md):
`SMWeylExtractionInput` transports the proved conditional compact coefficient
dimension identity to the existing actual local SM kernel. It assumes the
external `TorusReduction` law, a jointly continuous compact representation,
its semantic inverse-torus-character presentation, and a compact coefficient
comparison to the actual `LocalSpace`. The comparison/presentation/continuity
are application obligations, not established by the literature premise.
Kernel dimension, nonnegativity, column bounds, rank subtraction and positive-
multiplicity local support follow. No such complete SM input package is
constructed here; full residual classification and task III remain open.
No numerical dimensions or ranks are supplied as premises. Persistent audit:
`AuditSMWeylExtractionInput`, checking the conditional consequences only.


## Constructed SM compact extraction application

[Actual compact extraction](../../../../topics/sm-rank-certificates/compact-extraction-results.md):
`SMCombinedCompactAction` constructs the product gauge/independent-spin action
and its actual `LocalSpace` coefficient comparison. `SMCombinedCompactContinuity`
proves all ten field basis coefficient continuities, statistical source and
hypercharge-twisted Higgs model continuity, and the analytic coefficient
comparison. `SMCompactTorus` constructs the continuous six-circle dictionary.
`SMCompactMultiplicity.polynomial`/`presents` construct the actual finite
inverse-character presentation. The final local kernel dimension/rank/support
theorems retain only `Input`, the documented Weyl `TorusReduction` specialization;
comparison, joint continuity and character presentation are no longer supplied.
The reduction/root-maximal-torus Lie theorem itself remains unformalized.
The polynomial is a noncomputable spectral construction; no explicit species
weight recurrence or new numerical rank is claimed. Three-generation
multiplicity carriers remain fixed. Arbitrary residual invariance is a
separate condition. Persistent audit: `AuditSMCompactMultiplicity`.


## Existing q/l all-degree extraction support consumer

[Existing q/l extraction result](../../../../topics/sm-rank-certificates/ql-extraction-results.md):
`SMQLCompactMultiplicity.test_allowed_iff` composes the existing unconditional
scalar cyclic q/l residual separation with the constructed local multiplicity
extraction. For any positive cyclic order, q,l, content and constituent, full
support is exactly total q/l charge zero and extracted multiplicity positive.
`original_allowed_iff` and `original_forbidden_iff` retain the actual full-field
statistics and arbitrary Higgs counts, with a bounded constituent list. Their
only external mathematical premise is Weyl reduction for those bounded tests;
no extra residual-classification premise remains. The spectral construction is
noncomputable: concrete rank/support evaluation and the 572 recount are not
claimed, nor are other residual classes. Persistent audit:
`AuditSMQLCompactMultiplicity`, checking the conditional implications only.


## Fixed-input q/l prohibition/allowance requests

[Pattern facade result](../../../../topics/sm-rank-certificates/pattern-input-results.md):
`SMQLPatternRequests` constructs a finite product of actual full-group
coefficient tests selected by arbitrary B/L predicates on the existing signed
three-generation input, residual-neutral single Higgs and cyclic scalar q/l
action. `allowed_iff_original`, `forbidden_iff_original` and
`original_request_iff` prove the all-degree support semantics without external
inputs. Existing target signs/normalization and generic `Request` data are
preserved. `satisfies_iff` and `b1_b2_iff` use explicit Weyl reduction to give
finite universal exclusions and an independent allowed witness per target;
no carrier nontriviality/completeness premise is supplied. `forbid_of_charge`
is unconditional. Multiplicity is noncomputable; no numerical request checker
or particular q/l model satisfying B1-forbidden/B2-allowed is claimed. Generic,
charged-Higgs and LFV interfaces remain separate. Persistent audit:
`AuditSMQLPatternRequests`.

## Computable SM character presentation and q/l entry tests

[Computable character result](../../../../topics/sm-computable-characters/results.md):
`SMComputableSlotWeights.field_eigen` constructs the actual simultaneous
six-coordinate torus eigenbasis for all ten signed three-generation fields.
`SMComputableCharacter` implements inverse exterior/source/Higgs weight terms;
`SMComputableSupport.presents` proves their actual compact-model presentation
without literature input. No basis, weight multiplicity or presentation
certificate remains supplied. Integer extraction and Boolean q/l tests are
executable; only their `Finsupp` proof view is noncomputable.

Actual kernel/rank/local support and `SMComputableQLSupport`'s original Higgs
support and per-target request conditions retain the unchanged explicit Weyl
reduction input. The request criterion has a computable test per finite entry,
not an efficient enumeration of all contents. Kernel-checked bounded controls
include LLHH/conjugate LLHH and L4,m4,delta4; the latter gives conditional
kernel dimension 6 and rank 2469. Existing unconditional CSV entries/statuses
remain unchanged. The reference recurrence retains binomially many repeated
terms. Other residual classes and charged Higgs remain separate.
Persistent audit: `AuditSMComputableCharacter`.

[Sparse continuation](../../../../topics/sm-computable-characters/sparse-results.md):
`SMSparseCharacter` proves coefficient, presentation and multiplicity equality
with the reference for arbitrary contents, including a shared-table evaluator.
`SMSparseSupport` and `SMSparseQLSupport` preserve actual conditional kernel,
rank and q/l support semantics. `SMNeutralSparseRanks.inputs_enumerated`
kernel-checks the exact 107-row unresolved constant-species domain;
`kernel_dimension` and `rank_sound` prove the evaluator's uniform meaning under
the same Weyl input. All 107 outputs are obtained by compiled exact Lean
execution and independently cross-checked (41 positive, 66 zero). Those output
numbers are distinct from kernel-checked closed arithmetic equalities; see the
verification record for the arithmetic attempt. The old unconditional CSV is
unchanged: 19160 elementary parity/charge ranks, one nontrivial neutral rank
(1/108), and 107 unresolved rows. Full mixed-content and q/l request search
remain separate. Persistent audit: `AuditSMSparseCharacter`.

[Kernel-oriented evaluation](../../../../topics/sm-computable-characters/kernel-results.md):
`SMHiggsStringExtraction.multiplicity_eq` proves weak-Higgs-string/A2 cancellation
and sparse lookup compute the same integer as the original reference, for
arbitrary contents. `SMKernelWeightData` kernel-checks all 180 slot weights.
`SMNeutralSparseRanks.constant_source_row`, `columnsFast_eq` and
`solveDirectWith_data` remove constant-species identity factors and use mathlib's
proved fast binomial formula, while preserving the original evaluator for every
row. No new presentation, basis or multiplicity premise is supplied.

The former `SMNeutralSparseExamples.q_six` kernel-checked multiplicity 261 and
rank 5843115 for Q6,m2,delta=-2 at its numerical checkpoint; its actual
kernel/rank consumers retained the explicit Weyl input. That module and the
other closed numerical example module are now retired from builds at the
user's direction, with [source/audit snapshots](../../../../topics/sm-computable-characters/archive/remaining-numerical/README.md).
These exact example numerals are not active structural support claims.
The former Q18 exact column/multiplicity/rank declarations were
retired at the user's explicit selection of zero/nonzero support; their
[source snapshots](../../../../topics/sm-computable-characters/archive/q18-numerical/README.md)
and prior numerical verification are retained as historical evidence.
`SMGroupedCharacter.solveGrouped_eq` / `solveBounded_eq` and
`BoundedExteriorCoefficient.compute_eq` prove the algorithm changes uniformly;
linear support bounds are derived, never extra assumptions.
`SMCoefficientAssembly.factor` prevents assembly from re-expanding the closed
coefficient function. The all-107 closed arithmetic certificate was not
completed; the closed numerical route is retired.
Both existing CSVs retain their values and
the original unconditional classifier retains its scope/statuses. The current
strict audit covers the retained symbolic algebraic refinements and conditional
consumers. Removed numerical-example entries are preserved with their sources;
the retained strict axiom policy is unchanged.

[Structural support adapters](../../../../topics/sm-computable-characters/structural-results.md):
`SMConstantWeakCapacity.local_high_zero` and `kernel_high_finrank_zero` prove
vanishing for `m > min(n,speciesDimension−n)` on the actual local source/kernel
for all ten signed species and arbitrary supplied residual flavors. Their
balanced basis and constant-exterior transport are proved, with no Weyl input.
`SMGenerationCauchy` identifies the positive Q/L semisimple fields with three
generation copies, retaining independent weak/left/right factors and setting
U(1) to one. `SMGenerationSupport` constructs injective weak constituent maps
at Q degrees 6,12,18 and L degrees 2,4,6 uniformly over the bounded even weak
degrees. The subsequent non-numerical consumers below close the actual
coefficient/kernel connection and bounded original-Higgs/q/l iff statements.
Complementary degrees, signed conjugates and the arbitrary-m constituent iff
remain open. No all-content support
classification, new external theorem premise, rank-table certificate or
572-assignment search is claimed. Persistent audit: `AuditSMStructuralSupport`.
Capacity is the actual field-basis cardinality, with proved field-dimension
and existing ten-species convention identities. The structural import audit
excludes numerical rank classifiers, sparse/grouped evaluators and closed
neutral certificates; the Cauchy consumers use locally irreducible maps
through proved identities. These changes add no theorem premise.

## Structural Q18 coefficient support

[Q18 support results](../../../../topics/sm-computable-characters/q18-support-results.md):
`SMQ18LocalSupport.q18` proves nonzero actual kernel at positive Q18, weak
degree 6, delta -6 and trivial residual action. `kernel_allowed` and
`local_allowed` hold uniformly for even m <= 18 at delta -6;
`kernel_positive` and `rank_deficient` leave dimensions symbolic. No Weyl
input, numerical equality, character evaluation or new literature premise
is used. A determinant-one middle exterior pairing and the already proved
constituent embedding supply an actual nonzero functional; generic charge
cancellation restores U(1), and existing compact/local/kernel equivalences
preserve statistics and independent spin factors. Original Higgs admissibility
remains required. Other degrees/conjugates and necessary weak parity remain
outside this result. Strict audit: `AuditSMStructuralSupport`.

## Non-numerical original-Higgs support

[Non-numerical results](../../../../topics/sm-computable-characters/non-numerical-support-results.md):
`SMLowerHiggsSupport.lepton_ql_all_iff` classifies the actual original-field
space for every constant positive L degree n and arbitrary Higgs counts h,d:
`n • l = 0`, n even, n<=6, and h-d=n are necessary and sufficient.
`quark_ql_lower_iff` does the same for constant positive Q with n<=18:
`n • q = 0`, n even, and n+3*(h-d)=0. The existing scalar cyclic actions
and arbitrary positive cyclic order are retained. Companion theorems prove
the forbidden iff. Zero fermion degree is included. The final predicates
contain no unevaluated local Hom/multiplicity test.
`SMGenerationCoefficients` constructs the continuous models, weak self-duality
and actual source transport needed for compact Hom support reversal.
`SMLowerGenerationSupport` proves actual nonzero local coefficients/kernels
for Q6/Q12/Q18 and L2/L4/L6 at every bounded even weak degree and neutral
hypercharge. Local flavor actions are arbitrary and evaluated at identity;
only the scalar cyclic family is classified with its residual action retained.
No Weyl input, evaluated character, numerical rank/multiplicity premise or
new literature input is used. Upper-half Q, conjugates and mixed contents
remain outside this bounded iff. Strict audit: `AuditSMStructuralSupport`.

## Signed and mixed structural support

[Signed/mixed results](../../../../topics/sm-computable-characters/signed-mixed-results.md):
`SMQuarkAllHiggsSupport.original_ql_iff` extends the original-field Q criterion
to every n: residual n*q=0, n even, n<=24 and n+3*(h-d)=0.
`SMSignedHiggsSupport` proves the all-n conjugate Q/L criteria with the same
capacity/parity/residual conditions and reversed hypercharge. The previous
all-n positive L criterion remains valid. `SMAdmissibleConstantSupport`
additionally classifies the individual `QLFiniteSupport.Test` predicates in
all four families, with `Admissible h d m` retained: Q/conjugate Q require
m<=min(n,36-n); L/conjugate L require m=n. No extracted multiplicity or
unevaluated local Hom remains in those predicates.

`SMMixedConjugation.original_ql_iff` transports arbitrary mixed contents to
their signed opposites with h,d swapped; it is an equivalence/reduction, not
a classification of unknown contents. `SMChiralitySupport.original_forbidden`
excludes every content with an odd number of either chirality, for arbitrary
supplied residual flavors and all Higgs counts. Its independent-center test
uses the proved polynomial real-form comparison, not an assumed independent
Lorentz action. `SMMixedFamilySupport` identifies the existing actual four-family
spaces with the common original-field interface and proves the all-Higgs q/l
iff for DUQL/QQUE/QQQL/DUUE and their four conjugates: h=d and 3*q+l=0.
Its `factorwise_counterexample` shows that separate-species singlet permission
cannot be a necessary test for mixed permission. All these results retain
statistics and independent spin factors, use no numerical rank/multiplicity
or Weyl input, and add no external premise. General mixed classification is
not asserted. The continuation below discharges part of the
[previous branching gate](../../../../topics/sm-computable-characters/signed-mixed-stop.md);
joint labeled occurrence was open at that checkpoint. The later joint
continuation below supplies a Weyl-conditioned symbolic criterion; the
572-assignment search remains open.
Strict audit: `AuditSMStructuralSupport`.

## Constructed finite constituents for arbitrary mixed support

[Finite branching results](../../../../topics/sm-computable-characters/finite-branching-results.md):
`SMFiniteConstituentSupport.decomposition` constructs a complete finite
irreducible decomposition of the actual combined compact statistical source.
Its block count is bounded by the source dimension symbolically; color,
hypercharge, weak and independent spin actions are preserved jointly.
The Higgs constituent's irreducibility is proved by weak restriction.
`local_allowed_iff` and `kernel_allowed_iff` identify actual support with
equivalence of some source block to the Higgs model's dual.
`original_ql_iff` applies this criterion at all Higgs counts with the existing
finite weak/admissibility tests and scalar cyclic q/l neutrality.

`Matches` is an unevaluated representation-equivalence proposition, not an
executable classifier or an already decided support entry. No external Weyl
premise or new branching assumption is used in these implications.
`SMFiniteWeakBranching.certificate` separately constructs complete bounded
weak-SU2 sums for every actual statistical source; `constantCertificate`
also supplies the complementary bound `min n (dimension(s)-n)` for a constant
signed species, improving the upper-half Q/L bound. These weak-only copies
are not claimed to preserve the commuting color/spin/residual actions.
The later joint continuation below supersedes this opaque matching boundary
for the actual coefficient consumer. The assignment search remains separate.
Strict audit: `AuditSMStructuralSupport`.

## Joint mixed-content components and symbolic occurrence

[Joint branching results](../../../../topics/sm-computable-characters/joint-branching-results.md):
`SMCompactSpinBound` proves independent left/right torus bounds from actual
slots and the statistical quotient. `SMJointWeakContent` and `SMJointSpinContent`
construct three complete isotypic decompositions, preserving color and
hypercharge on the final canonical multiplicity. Weak and left/right labels
are bounded by the existing weak bound and the actual chirality slot counts.
`SMJointOccurrence.hom_allowed_iff` retains the entire colored target and
eliminates the three SU2 matches. `SMJointCoefficient.local_allowed_iff`
identifies actual Higgs coefficients with Hom from the (m,0,0) multiplicity
to the proved inverse hypercharge/color-trivial line. These results use no
Weyl premise or numerical evaluator. Strict audit: `AuditSMStructuralSupport`.

`SMJointAlgebraicSupport.Occurs` is an explicit six-color-term by eight-spin-term
symbolic coefficient condition, using the actual ten-species statistical
character presentation. Under exactly the existing coefficient-model Weyl
`Input`, `joint_allowed_iff`, `matches_iff`, `kernel_allowed_iff` and
`original_ql_iff` eliminate remaining opaque Hom/block-equivalence propositions
from the actual support consumer at all Higgs counts. The final right side
contains only cyclic q/l neutrality, bounded Higgs admissibility and this
coefficient's nonvanishing. No exact positive multiplicity is required.

`SMJointColoredSupport.joint_allowed_iff` additionally handles any specified
colored target with three bounded SU2 labels, given its verified torus terms,
joint continuity and the same Weyl theorem specialized to the Hom model.
That specialization is not derived from the coefficient-model `Input`.
For reducible targets it tests a shared constituent, not inclusion of the
entire target. A catalogue of all colored highest weights, a simplified
partition criterion, concrete entry decisions and the 572-assignment search
are not supplied. No closed numerical rank/multiplicity certificate is used
or rebuilt. Strict optional audit: `AuditSMJointAlgebraicSupport`; its
conditional implications do not prove the external Weyl premise.

## Decided structural mixed regions

[Structural classification results](../../../../topics/sm-computable-characters/structural-classification-results.md):
`SMMixedWeakCapacity.source_bounded` sharpens the mixed weak bound to the sum
of specieswise `min(c_s,D_s-c_s)` for doublets and zero for singlets.
`local_high_forbidden` and `original_ql_forbidden` prove actual local/all-Higgs
coefficient vanishing above that bound. If all doublet species are empty or
full, all cases h != d are forbidden, regardless of other species' occupation.
`SMContentCapacity.source_allowed_iff` proves the statistical **source** is
nonzero iff every count fits its field dimension. This alone is not invariant
permission. Overflow makes every local and original q/l coefficient vanish.

`SMSaturatedContentSupport.original_ql_iff` completely decides the subfamily
where every species is empty or fully occupied: actual original support iff
h=d, actual hypercharge is zero and actual q/l charge is zero. Its proof uses
the structural zero/top exterior line identity, proved triviality of continuous
lines on the semisimple compact factors and the existing actual charge actions.
No positive multiplicity or invariant witness is assumed. The dimension-one
identity is symbolic; no large binomial or rank numeral is evaluated.

`SMSignedBalance` proves opposite matching counts cancel both charges at every
cyclic order, including even order. Saturated balanced contents, including the
fully occupied signed universe, therefore have original support exactly when
h=d. Balance alone for partially occupied mixed contents is not sufficient
here. No Weyl input, new literature premise, numerical evaluator or closed
certificate is used. Strict audit: `AuditSMStructuralSupport`.

The original full q/l support classification remains unfinished for general
fitting, partially occupied mixed contents outside the proved families and
exclusions. The [remaining positive branching interface](../../../../topics/sm-computable-characters/structural-classification-boundary.md)
is recorded explicitly; neither it nor general Kronecker positivity is assumed.

## Complete generation reduction for the actual signed fields

[Limited foundation results](../../../../topics/sm-computable-characters/limited-foundation-results.md):
`SMGenerationExhaustion.actual_field` identifies each of the ten actual compact
signed fields with its gauge/spin core tensored with trivial `Flavor_3`.
`exists_nonzero_bounded_factor_iff` reduces arbitrary equivariant target maps
from an exterior power to a realizable triple of single-generation exterior
powers with the same total degree and each count bounded by the core dimension.
Color, hypercharge, weak and independent two-spin actions are preserved.
`source_nonzero_iff` concerns the tensor source only, not invariant permission.
All dimensions stay symbolic; no Weyl input, numerical proof or new literature
premise is used. Joint target occurrences and full mixed q/l classification
remain open. Strict audit: `AuditSMStructuralSupport`.

The [joint lepton continuation](../../../../topics/sm-computable-characters/lepton-joint-results.md)
discharges all weak/left-spin target occurrences for the actual constant-L
source. `SMLeptonCoreBranching.source_target_iff` proves closed degree,
complementary-capacity, sum and parity conditions under the complete retained
semisimple group, with the independent right spin preserved. Field/projection
identifications and surjectivity are proved. This is a joint constituent
theorem, not permission for a scalar mixed operator before its other spin,
color and charge conditions are checked. Hypercharge and residual charges
retain their existing consumers. Colored/mixed occurrences remain open.
No Weyl input or numerical proof is used. Strict audit: `AuditSMStructuralSupport`.

The [signed mixed-lepton continuation](../../../../topics/sm-computable-characters/mixed-lepton-results.md)
proves actual all-Higgs support for arbitrary L/conjugate-L occupations and
ordering under every existing scalar cyclic q/l assignment. With
C(n)=min(n,12-n), permission is equivalent to a,b<=12, both even,
h-d=a-b, a*l-b*l=0 and |a-b|<=C(a)+C(b). The proof constructs nonzero
coefficients through irreducible-target gluing and charged Clebsch--Gordan
embeddings, and proves necessity using actual capacity, separate chirality
centers and charge/weak bounds. No unknown `Allowed`, numerical rank or
multiplicity, Weyl input or new literature premise remains in this family.
Other mixed families and the complete colored q/l classification remain
open. Strict audit: `AuditSMStructuralSupport`.

The [colored-square continuation](../../../../topics/sm-computable-characters/colored-square-results.md)
identifies actual signed U/D and conjugate-U/D core square/fourth-degree
branches under the retained semisimple group, with left and right spin
projections distinct. `SMColoredPairHiggsSupport.original_ql_iff` proves
actual U^2 conjugate-U^2 and D^2 conjugate-D^2 permission exactly when h=d,
for all Higgs degrees and all existing cyclic q/l actions. The proof uses
nonzero coupled colored coefficients, a surjective generation projection,
actual statistical-source transport and hypercharge/residual consumers.
Symmetric color-square irreducibility is not assumed. No numerical rank,
multiplicity or new external input is used. This closes these two colored
mixed contents, not the full original q/l classification. Strict audit:
`AuditSMStructuralSupport`.

The [middle-cube continuation](../../../../topics/sm-computable-characters/colored-cube-results.md)
adds `SMColoredCubeBranching.positiveCube` and `negativeCube` for actual
signed U/D core species 1,2,6,7. These are complete semisimple equivariant
decompositions with distinct right/left spin projections. The middle color
branch is actual trace-free End(color), or End(dual color) for conjugates;
no irreducibility or matching rule is assumed. No new charge/Higgs support
iff is claimed by these adapters. Q-core branching and complete mixed
color couplings remain open. Strict audit: `AuditSMStructuralSupport`.

The [Q-square continuation](../../../../topics/sm-computable-characters/colored-completion-results.md)
adds `SMQCoreBranching` for actual Q/conjugate-Q squares and their degree-ten
complements, with separate weak and left/right spin projections.
`SMQPairHiggsSupport.original_ql_iff` proves actual three-generation
Q^2 conjugate-Q^2 permission iff h=d for every existing cyclic scalar q/l
action. Opposite-color scalar-spin branches couple through a nonzero
coefficient after surjective core/generation projections and actual
statistical-source transport. No separate core singlet, unknown Hom,
Weyl input or numerical certificate is assumed. The original full mixed
q/l classification remains open. Strict audit: `AuditSMStructuralSupport`.

The [arbitrary-dimension cubic bridge](../../../../topics/sm-computable-characters/colored-middle-results.md)
adds `SMQCubeBranching.positiveCube`, `negativeCube`, `positiveNine` and
`negativeNine` for actual signed Q/conjugate-Q core species 0 and 5.
These are exhaustive coarse semisimple equivalences with independent weak
and left/right spins. The [further resolution](../../../../topics/sm-computable-characters/colored-cubic-resolution-results.md)
adds the four `SMQResolvedCubeBranching` equivalences: all six actual
color/weak/spin branches of signed core degrees three/nine are resolved.
The hook source comparison and finite-length cancellation are proved in
the Math layer. The [quartic resolution](../../../../topics/sm-computable-characters/colored-quartic-resolution-results.md)
adds `SMQQuarticBranching.positiveFourth`, `negativeFourth`, `positiveEight`
and `negativeEight`. Both quartic color/weak kernels are resolved into
fixed actual color factors and weak labels, with the independent spin
kept throughout. The new color factor is an actual nonzero symmetric
contraction kernel; its general products are not assumed classified.
The subsequent signed fifth/sixth results are linked below; full mixed
color support remains open; no new
all-Higgs permission iff is claimed. No numerical rank, Weyl premise or
new literature input is used. Strict audit: `AuditSMStructuralSupport`.

The [fifth-degree assembly](../../../../topics/sm-computable-characters/colored-fifth-assembly-results.md)
adds `SMQFifthBranching.positiveFifth` and `positiveSeventh` for the actual
signed species-0 core, retaining color, weak and left-spin actions. Its
complete source comparison is proved with no branching or matching premise;
the subsequent result closes the conjugate and sixth source obligations.

The [sixth/conjugate result](../../../../topics/sm-computable-characters/colored-sixth-results.md)
adds `SMQSixthBranching.positiveSixth`, `negativeSixth` and the two signed
fifth/seventh adapters. The actual exterior-dual equivalence reuses mathlib's
proved perfect pairing and adds its full-group equivariance; no new
literature premise or numerical certificate is introduced. The general
compatible positive color-coupling rule and full mixed q/l consumer remain open.

`SMQJointPresentation` transports the complete joint expressions to the
actual retained single-generation Q/conjugate-Q cores (signed species 0/5),
at every exterior degree and weak Higgs constituent degree. The support iff
has only finite joint choices, positive color diagrams and SU2 paths on its
right side. No Weyl or numerical rank/multiplicity input is used. The
three-generation mixed source and original full q/l consumer are not yet
composed by this result. See
[Q joint results](../../../../topics/sm-computable-characters/q-joint-presentation-results.md).

`SMSignedCoreJointPresentation` now supplies every exterior degree of all
ten actual signed single-generation cores, including conjugates and zero at
overflow. `SMJointContentSupport.sourceEquiv` constructs the actual mixed,
three-generation statistical-source comparison, and `restricted_iff`
removes all remaining semisimple occurrence tests in favor of finite positive
occupation/component/color-diagram/SU2-path conditions.
`SMJointHiggsSupport.original_ql_iff` and `original_ql_forbidden_iff` complete
original endpoint 2 for arbitrary contents and Higgs bidegrees, every
nonzero cyclic modulus and the existing scalar q/l assignments. They retain
Higgs admissibility, hypercharge and residual neutrality exactly and use no
Weyl, numerical rank/multiplicity or new literature premise. Arbitrary
residual flavor representations are not classified: endpoint 1 continues
to retain `Allowed(T)` for those parameters. This is derivative-free
coefficient support, not UV generation, rates or numerical phenomenology.
See the [proof dossier](../../applications/Physics/SM_STRUCTURAL_QL_SUPPORT.md)
and [verification](../../../../topics/sm-computable-characters/full-support-verification.md).

## Opt-in compact structural support decisions

`SMCompactSupportDecision.contentDecision` and `higgsDecision` decide the
existing structural predicates with compact three-generation occupations;
they introduce no source comparison, Weyl, numerical or occurrence premise.
`SMCompactSupportExamples.q18Allowed` and `mixedForbidden` are kernel-checked
actual original-space examples for k=1,q=l=0 and the fixed signed SM/Higgs
input. The definitions remain noncomputable for general compiled evaluation.
Focused builds, strict audits and the user-authorized full library build pass.
See the
[scope and verification](../../applications/Physics/SM_COMPACT_SUPPORT_DECISION.md).

## Executable SM data support connection

`Physics.SMCoreSourceData.corePresentation` puts the executable ten-species core
syntax in its outer field, with actual equivalences supplied by the existing
mathematical decompositions. `Physics.SMJointSupportData.dataSupport_iff` proves
full joint content support equivalence, and `higgsDataSupport_iff` and
`original_ql_iff` retain all Higgs degrees and the original scalar cyclic q/l
residual/hypercharge equations. No external Weyl, numerical table or supplied
occurrence premise is introduced. Data composition is executable; generic
support decision functions are unchanged. New proofs and consumers use
ordinary lemmas and explicit source/Higgs choices, without computational
support proofs. Thirty-four named Physics declarations and the two-declaration
Math helper are strictly audited. The
[dossier](../../applications/Physics/SM_JOINT_SUPPORT_DATA.md) and
[bounded consumer verification](../../../../topics/sm-support-evaluator-feasibility/data-connection-results.md)
state the exact semantics and measured resource scope, which excludes arbitrary
witness search. Other dictionaries, derivatives and UV realization are unchanged.

## Charge and engineering-dimension lower bounds

`Physics.SMChargeDegreeBounds.charge_degree` proves `|B3|+|L|≤n` for every signed
pattern, without a nonzero-support premise. `original_degree_lower` connects
an explicit arithmetic minimum-|L| gate to all actual allowed original
coefficients at arbitrary Higgs bidegree. Closed gates are kernel-proved by
the opt-in assignment verifier; generic gates remain explicit parameters.
`twiceDimension` is the grading `3*n+2*(h+d)`, not an anomalous dimension or
rate. No claim that this lower bound is attained is made. All 13 public
declarations have a persistent strict transitive audit. See the
[dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md) and
[maintenance topic](../../../../topics/sm-finite-charge-support/README.md).

## Exact finite B1/B2 lepton-charge support

`Physics.SMFiniteLeptonSupport.exact_original_iff` classifies the exact (B3,L)
selector at B3=3 or 6 for the unchanged three-generation derivative-free
signed SM/Higgs scalar cyclic q/l input. Its attainable L sets are all odd
|L|≤17 and all even |L|≤18 respectively; all 37 values have committed
kernel-checked full joint witnesses. `original_allowed_iff` covers absolute
B3 via arithmetic sign normalization and `b1_b2_iff` covers the existing mixed
request, uniformly for arbitrary nonzero k,q,l. No supplied occurrence,
multiplicity or Weyl premise is used. `SMFiniteLeptonAssignments` now defines
the candidate domain and verdicts entirely in Lean, without a supplied table
or CSV. It proves exact membership, unique coverage, total 572 and the
326/144/102/0 classification counts, with original-space class equivalences
and derived B1/B2 totals. The normal full build includes their persistent
audit. CSV export is optional output and is not a theorem premise.
This does not determine minimum dimension, UV
generation, rates or derivative support. See the
[dossier](../../applications/Physics/SM_FINITE_LEPTON_SUPPORT.md) and
[proof topic](../../../../topics/sm-attainable-lepton-charges/README.md).

## Minimum absolute lepton charge and default-build degree bounds

`Physics.SMFiniteLeptonDegreeBounds.minLepton` is a computable Option Nat over
the neutral members of the proved finite range. For b=3 or 6 and arbitrary
nonzero k,q,l, None iff original prohibition and Some m is attained in an
actual exact-(B3,L) coefficient space. The lower-bound proof normalizes the
sign of B3 while preserving the actual |L|; it covers every selected original
content and Higgs bidegree. It gives n≥b+m and twice engineering dimension
≥3*(b+m), with no external arithmetic gate, occurrence, rank or CSV premise.
The ordinary build proves all 796 allowed row/target applications, the full
minimum-|L| distributions and the 278 B1 / 284 B2 high-degree group counts.
These remain lower bounds on total operator dimension. The persistent audit
includes all new declarations and importing examples; the base count audit
is unchanged. See the [degree dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md)
and [review-response plan](../../../../topics/sm-finite-charge-support/minimum-lepton-plan.md).

## Four exact minimum operator dimensions

`Physics.SMMinimumOperatorDimension.IsMinimum` requires actual original coefficient
allowance at doubled dimension M and a universal lower bound over all selected
contents, both signs of B3 and all Higgs bidegrees. In the unchanged fixed
ten-species, three-generation, derivative-free SM with independent Lorentz
actions, neutral-residual Higgs/dual and scalar cyclic q/l action, the proved
minimum dimensions are: B1 at (k,q,l)=(2,0,0): 6; B2 at (2,0,0): 9;
B1 at (3,1,1): 9; B1 at (5,1,1): 10. Positive witnesses retain full joint
statistics and actual source transport. The last lower bound additionally
uses a proved signed-hypercharge dictionary inequality and the existing
charge/parity/hypercharge conditions, without a source-conjugation premise.

No new mathematical premise, multiplicity law, numerical/CSV input, axiom
exception or physical extension is added. These four exact minima do not
classify all cyclic inputs or all 572 assignments and imply no UV generation
or observable rate. The persistent strict transitive audit includes importing
consumers. See the [degree dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md)
and [topic results](../../../../topics/sm-minimum-operator-dimension/results.md).

## Complete B1 support below dimension ten

`Physics.SMB1BelowTen.allowed_iff` proves actual B1 allowance strictly below
engineering dimension ten iff `3*q+l=0 ∨ 3*q-l=0 ∨ 3*q+3*l=0` for arbitrary
nonzero cyclic k, on the unchanged fixed signed three-generation SM,
derivative-free, neutral-residual Higgs/dual and scalar q/l dictionary.
The complementary universal prohibition covers both baryon signs and every
content/Higgs degree under the strict bound. Necessity uses charge-degree,
parity and the proved hypercharge envelope; sufficiency uses actual joint
support at dimensions six/seven/nine and original-space transport.

`SMB1BelowTenAssignments` inherits unique complete coverage of the existing
572 assignments and proves 146 below-ten allowed and 426 below-ten forbidden
rows. The latter comprise 180 all-degree-allowed and 246 all-degree-forbidden
rows, with explicit original-space class equivalences. No numerical/CSV,
multiplicity, new axiom or source-conjugation premise is added. No general
minimum-dimension classification, arbitrary flavor-action classification or
UV/rate consequence is asserted. See the [degree dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md)
and [topic](../../../../topics/sm-b1-below-ten/results.md).

## Retained B1 dimension intervals and resource boundary

`Physics.SMB1MinimumClassification.row_certificate` supplies attained actual
upper grades and universal lower grades for every one of the 326 allowed
rows of the existing 572-row domain. Both baryon signs and every original
content/Higgs degree are included. The kernel proves 160 matching bounds,
yielding actual exact minima through `row_exact`, and 166 unresolved intervals.
The 246 all-degree-forbidden rows retain None. Selected upper witnesses have
proved joint color/weak/both-spin statistics and original-space transport.

`SMB1DimensionBounds.original_grade_congruence` proves the grade congruence
from actual independent chirality, without a new premise. The retained row
lower bounds use the existing charge bound and below-ten prohibition. A
proposed stronger weak-envelope connection hit the frozen 10 GiB guard and
is excluded from active theorems. Its diagnostic apparent all-row matches
are not minimum certificates. At that checkpoint the full 326-minimum goal was unachieved;
the subsequent revision below closes it with independently checked proofs.
No new axiom, supplied occurrence/multiplicity law, numerical/CSV premise,
dependency or physical extension is introduced. See the
[degree dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md) and
[stopped topic](../../../../topics/sm-b1-minimum-classification/results.md).

## Complete B1 minimum grades on the existing finite domain

`Physics.SMB1WeakDimensionBounds.original_weak_envelope` proves
`abs(7*L-B3)≤12+twiceDimension` for actual original allowance on the same
fixed SM/Higgs dictionary. Abstract ten-count arithmetic, separately proved
dictionary sums and existing complementary weak-capacity extraction keep
representation terms out of the arithmetic proof. No new representation
foundation or support premise is introduced. `SMB1StrongDimensionBounds`
combines this with existing signed charge/hypercharge/grade congruence facts.

`SMB1ExactMinima.row_minimum` proves attained actual minima and universal
lower bounds for all 326 allowed B1 rows of the inherited 572-row domain;
both baryon signs, every content and Higgs bidegree are included. The
remaining 246 rows have None iff all-degree prohibition. Kernel distribution
counts at engineering dimensions 7/9/10/14/15/19/20/24/27/31 are respectively
48/98/62/28/16/16/10/28/10/10. No numerical/CSV input or new witness search
enters this result; previous graded actual witnesses are unchanged.

The previous resource-stop record remains valid history, while the revised
proof closes its finite-domain endpoint with unchanged limits/pins. The
strict transitive audit includes actual bridges, arithmetic helpers and
fresh importing consumers. This does not establish arbitrary-k minimum
classification, arbitrary residual flavor actions, B2 minima, derivatives,
UV generation or rates. See the [degree dossier](../../applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md)
and [revision results](../../../../topics/sm-b1-weak-connection/results.md).

## Baryon-triality component restriction

[Conditional-input dossier](../../applications/GUT/CONDITIONAL_MODEL_INPUT_CHECKS.md):
`BaryonTrialitySMInput` uses the declared signed SM fermions and charged
Higgs/dual, with Z3 copy actions on arbitrary complex modules. An integral
charge identity and actual hypercharge invariance force 9 to divide 3B for
nonzero coefficients; absolute B1/B2 coefficient and residual-Hom spaces vanish
at all mixed degrees. The physical component charges match the specified
non-R B3 convention. SUSY/FN spectra, anomalies and a UV single-light-Higgs
identification are not proved. P6 reuse checks the inverse-generator component
dictionary against existing BGW; it does not prove a full literature model.

## Dev–Mohapatra Selected Source Connection

The [connection dossier](../../applications/Physics/DEV_MOHAPATRA_CONNECTION.md)
closes the full SM-cover/Lorentz/parity action on the earlier witness and
constructs a selected literal color/right-Weyl contraction with exterior
statistics and nonzero physical evaluation. The local C-inverse dictionary
is explicit; the antisymmetric two-flavor dictionary is proved. Full
flavor-summed UV matching, four-component normalization and the printed
scalar prefactor remain unproved. A supplied scalar is not a generated law.

The subsequent [bounded tree-level result](../../../../topics/dev-mohapatra-coefficient-connection/tree-level-results.md)
derives a generated polynomial from an explicitly supplied one-N chiral
action, with nonzero scalar mass-squared, Majorana mass and selected couplings.
The actual 18-component Grassmann term is nonzero. Its literal uu/ds/ds
prefactor is `(lam lamDS)^2/(2 mChiSq^2 mN)`. The Majorana half, cubic odd
anticommutation, and ordered d,s flavor-sum doubling are proved, not literature
premises. The scalar quadratic term, vertex signs, right-Weyl dictionary and
selected coupling normalization are supplied action conventions. Equality of
that dictionary with the paper's suppressed conventions, full Hermitian/flavor
matching and physical-intertwiner polynomial transport are not proved.
The 8 pi² comparison is conditional; no unconditional paper error or rate
conclusion follows. The previous supplied-scalar consumer is unchanged.

The subsequent [source inspection](../../../../topics/dev-mohapatra-coefficient-connection/convention-results.md)
recovers the printed chi-bar/chi placement and explicit Majorana half.
No proof hypothesis is removed: C-inverse/action phase, selected flavor-sum
normalization and the kinetic/action dictionary remain external.

The Dev–Mohapatra signed adapter supplies the existing Euclidean C matrix
and its right projector: C inverse = -C. Its mass, vertex and target sign
translations and common bilinear rescaling are proved. This choice does not
recover the source's canonical kinetic, Minkowski or Hermitian conventions;
the scalar quadratic parameter remains supplied.

The literature-informed Dev–Mohapatra adapter proves explicit C matrices
from the inspected related sources and their lower/right inverse-C pairing.
Adoption by the target, canonical physical mass/field normalization, scalar
normalization and printed-to-component coupling identification remain inputs.
The signed ratios are action coefficients; no Lagrangian/Hamiltonian sign
choice is inferred for the target. Existing conditional kinetic-half tools
are audited, without asserting a new derivative/IBP or full action bridge.

The fixed external-leg mass-inverse contraction uses the same supplied
chiral vertices and masses and proves agreement with their sequential
elimination. It is not a kinetic-propagator/LSZ/S-matrix theorem. The conjugate
completion is a supplied complexified polynomial; its projection requires
explicit images of vertices and, for full chiral equality, zero image of the
conjugate heavy variable. Neither the actual H.c. dictionary nor commutation
of full stationary elimination with projection is inferred.

The [Hermitian action phase](../../../../topics/dev-mohapatra-coefficient-connection/hermitian-results.md)
assumes a complex algebra with compatible StarRing/StarModule, real nonzero
scalar mass, and supplied vertices. Exact scalar elimination and H.c. are
proved for this interface. Its concrete 36-external/four-heavy Grassmann
stationary check is a degree-six diagnostic in two rational cases, not a Lean
premise, physical-carrier star construction or all-degree heavy elimination.

The [all-degree heavy-elimination phase](../../../../topics/dev-mohapatra-coefficient-connection/heavy-elimination-results.md)
constructs the 36-external/four-heavy complex exterior conjugation. Concrete
kernel nilpotence, stationary solution, uniqueness, H.c. of that solution
and its genuine algebra-homomorphism substitution are proved. The original
scalar action requires real nonzero m and heavy elimination requires nonzero
M; couplings may be arbitrary complex values. No diagnostic premise, assumed
heavy inverse, zero barred-heavy input or degree truncation is used. The
literature action dictionary and derivative-free scope remain explicit.

The [normalization closure](../../../../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md)
connects a proved nonzero literature operator and the exact projected action.
The multiplier-family matching iff assumes nonzero original masses/couplings
and nonzero mass multipliers; invertible source identifications also require
nonzero vertex/operator multipliers. The canonical and ordered flavor
ratios remain conditional on the source dictionary, not paper-error claims.
[Unit-phase and bounded-magnitude obstructions](../../../../topics/dev-mohapatra-coefficient-connection/review-closure-results.md)
use the explicit multiplier family and their stated norm bound; unrestricted
rational/algebraic compensation and physical source adoption remain unproved.

## Li six-quark normalized probe decomposition

`LiSixQuarkProbeDecomposition` splits the independently defined local 5-by-5
array into `ker extraProbeLinear` and the line with normalized generator `extra`.
It uses the existing explicit probe, `extraProbe_extra = 1`, linearity and
finite-dimensional rank-nullity. Its kernel dimension is 24 without importing
`LiSixQuarkFiniteData`, `LiSixQuarkOrbitData` or the selected-orbit basis.
Small coordinate proofs of the probe normalization remain in its ancestry.
Its independent audit excludes the selected-orbit modules as imports.

The split alone does not identify the printed orbit span. That identification
now uses the constructed source/orbit basis and symbolic block extraction,
rather than the former dense certificate. `printedSpan_eq_kernel`, literal
reconstruction, exchange and flavor-boundary consumers retain their original
statements and physical scope. See the
[source derivation](../../../../topics/proof-readability-review/source-derivation.md).

## Structural Li exchange and product blocks

`LiSixQuarkExtension.extra` is now the pairing of two explicit color/spin
vector pairs. Its exchange property follows from their two-dimensional block
actions and a symbolic tensor identity. Five-coordinate scalar checks of the
named vector actions remain; no dense rank/inverse certificate enters this
proof. `LiSixQuarkPairBlock` reconstructs the four-dimensional product and its
three-generator probe kernel with symbolic formulas in arbitrary coefficients.
`LiSixQuarkBlockCoordinates.localBlocks` splits local arrays linearly into
2-by-2, 2-by-3, 3-by-2 and 3-by-3 tensor products. `LiSixQuarkExchangeBlocks`
supplies the even/odd exchange decomposition through actual slot permutations.
These results add no physical hypothesis or printed-orbit completeness premise.
The selected-orbit basis is now connected to these blocks through actual raw
epsilon sources, uniform factored Young actions and nineteen scalar source
amplitudes. Its forward columns are constructed from exchange words, and its
inverse is the small-block extraction map. The cached seed and dense matrix
tables and their closed certificates are removed. Independent source-import
and transitive consumer-dependency audits preserve that separation, including
private helpers. This changes the proof route, not the model hypotheses.
See the [source derivation](../../../../topics/proof-readability-review/source-derivation.md).

## Constructed mass-transport certificates

[Equality transport](../../../../../Physics/FieldTheory/Mass/Algebra/SymmetricMassTransport.lean)
now packages its existing mass equality, nonvanishing and radical
representation results in a constructed certificate. The existing
[pullback certificate](../../../../../Physics/FieldTheory/Mass/Algebra/EquivariantWeylMassTransport.lean)
also proves radical membership from its form equality. Neither construction
adds a supplied certificate or a new theorem hypothesis: both are derived
from the original equality or representation equivalence and mass.
The [compatibility record](../../../../topics/derivative-ibp/dependency-integration.md)
records the concrete consumers and strict transitive checks.

## Generation Coefficient Compatibility

`SMGenerationSupport.generation_triple` composes injective intertwiners before
specializing a field action. The existing Q18/L6 injections keep their statements
and hypotheses. The [independent audit](../../../../../Physics/StandardModel/Operators/Support/Decomposition/Audit/AuditSMGenerationSupport.lean)
checks nine declarations transitively against the standard axiom policy.
The presented-generation coefficient helper retains both the generation
representation and the actual source as explicit parameters, with proved
equivalences to a common presentation. Q18 supplies its dimension 36,
determinant one and middle exterior self-duality on a distinct carrier.
The producer and local consumers compose before specializing the exterior
degree. The [connection audit](../../../../../Physics/StandardModel/Operators/Support/Coordinates/Audit/AuditSMCarrierConnection.lean)
checks 20 declarations, including the actual species-zero equivalence,
Q18 coefficient, lower-generation local coefficient and Q18 local kernel.
Public conclusions and their parity, degree-range and hypercharge hypotheses
are unchanged. No external theorem premise, new physical assumption or
derivative/IBP statement is introduced. See the
[carrier pilot](../../../../topics/derivative-ibp/carrier-pilot.md).

[ProjectedWeylMass](../../../../../Physics/FieldTheory/Mass/Algebra/ProjectedWeylMass.lean)
defines the bilinear form from heavy field/dual projections and proves equality
with the split mass pullback. Its radical-membership lemma requires an actual
mass, a proved equality with that form and a vanishing heavy projection.
The ScalarBlock consumer proves these conditions for the existing mass;
the helper does not construct a replacement physical mass or supply a new
mass-form premise to that public theorem.

## Algebraic Lorentz Jets And Free Massless Scalar EOM

The [Lorentz/EOM consumer](../../core/Physics/LORENTZ_SCALAR_EOM_IBP.md)
uses the existing actual SL(2,ℂ), left Weyl and entrywise-conjugate right Weyl
actions. A proved Pauli-coordinate equivalence transports `A ↦ M A M†` to
four coordinates, preserving the real Minkowski subspace and signature
`(+,-,-,-)`. Derivative source vectors carry the explicit dual action
`c_ji(g)=L(g⁻¹)_ij`. Their covariance and scalar contractions are proved in
the actual jet algebra. No compactness, averaging or classification of the
topological cover is assumed or concluded.

The massless scalar symbol is explicitly `p₀²-p₁²-p₂²-p₃²`; its invariance is
proved for this action. The equation defines a free algebraic scalar model,
with all derivative descendants. The EOM-ideal and generator/free-algebra
presentations, induced derivatives, equivariant IBP coefficient descent and
combined source/representation equivalence are checked. The kinetic term is
an actual divergence modulo EOM. Every pure time jet remains nonzero in the
on-shell generator module and algebra before IBP, so higher jets are not
truncated. These controls do not classify all four-dimensional invariants.

The [physical audit](../../../../../Physics/FieldTheory/Jets/Lorentz/Audit/AuditLorentzScalarEOM.lean)
checks 67 declarations transitively using only the standard axioms and rejects
GUT imports. The narrow local Pauli adapter does not certify the larger
Physlib Lorentz/SM closure or equality with its coordinate map. Massive,
interacting or Weyl EOM, gauge curvature/Bianchi, disconnected Lorentz actions,
variational derivation, analytic actions, amplitudes and EFT counting remain
outside the result. No external physical or literature completeness premise
is introduced.

## Constant Finite-Group Spurions On Scalar Lorentz Jets

The [jet/spurion connection](../../../../topics/jet-spurion-evaluation/results.md)
specializes actual scalar EOM/IBP evaluation to the same four-dimensional
Pauli SL(2,ℂ) dual direction action. Its wave-symbol invariance is proved;
the residual internal group and finite component representation remain
parameters. Local and residual actions are constructed on the source before
relations. Local coinvariants avoid averaging the noncompact local group.

For each specified constant, locally neutral spurion value, polynomial
evaluation is onto all local-invariant and actual-residual-stabilizer-invariant
coefficients, with sufficient degree at most orbit size minus one or group
order minus one. The [physical strict audit](../../../../../Physics/FieldTheory/Jets/Lorentz/Audit/AuditLorentzSpurionEvaluation.lean)
checks this specialization and its source pullback with the standard axiom
policy. The separate sharp degree-one sign example uses a one-direction mixed
source and trivial local group; it is not a complete 4D invariant basis.
These conclusions concern algebraic coefficient spaces, without matching,
amplitudes, rates, interacting/Weyl EOM or generic algebraic-group saturation.

## Free Left-Chiral Weyl Equations And Actual EOM/IBP

The [Weyl extension](../../../../topics/linear-eom-weyl/results.md) uses the
existing SL(2,ℂ) fundamental component action and dual four-direction action.
A dual Pauli contraction and first-jet frame prove seed covariance with the
dual right-spin equation representation. The explicit first-order seeds and
their off-shell nonzero values are proved. Their quotient relations include
every ordinary derivative descendant; wave relations on both components are
consequences, not substitutes for the first-order system. No covariance or
completeness assertion from literature is assumed.

A null-symbol polarization probe detects pure time jets of every order after
EOM, before IBP. The generator, exterior and actual mixed algebra controls
are nonzero. Free scalar spectators use a zero seed. The same actual algebra
projection, finite image grades, even derivatives and inverse equivariant
EOM/IBP source comparison feed coefficient descent. These are source-vector
and algebraic-dual statements, without an imported classical-field/index
dictionary or a claimed nonzero one-field Lorentz-invariant integrated term.
The [physical strict audit](../../../../../Physics/FieldTheory/Jets/Weyl/Equations/Audit/AuditWeylLinearEquation.lean)
rejects GUT imports and permits only the standard axioms. The endpoint is one
free massless chiral field; right/conjugate or massive/interacting equations,
gauge curvature/Bianchi, amplitudes, full EFT counts and matching/rates remain
separate work. The literature register preserves inspection/comparison limits.

## Conjugate Weyl Jets, Adjoint And Complete Null IBP Consumer

The [conjugate Weyl dossier](../../core/Physics/WEYL_CONJUGATE_IBP.md) keeps the
same free massless equation, signature and actual SL(2,ℂ) source/dual convention.
The right seed and dual left equation action are constructed; covariance and
reality of the direction coefficients are proved. Conjugation identifies the
entire left/right descendant modules, with inverse semilinear quotient maps
commuting with shifts and the actual group actions. No physical covariance,
rank, completeness or classical field-index dictionary is assumed.

On the paired odd exterior algebra, the chirality swap defines the Hermitian
adjoint. Its involution, product reversal, semilinearity, derivative and Lorentz
compatibility, projection compatibility and preservation of the linear IBP
range are proved. Its IBP descent concerns an ungraded vector-space quotient,
without a product of IBP classes. Arbitrary even-system adjoints, analytic
operator adjoints and interacting/massive or gauge-covariant equations remain
outside the result.

The separate actual four-dimensional single-left-Weyl consumer proves the
complete positive-order EOM/IBP source zero, with dimension zero, empty basis
and zero invariant coefficients. Its first jet survives EOM and dies under
IBP. This does not enumerate multi-field interactions or supply amplitudes,
UV matching or rates. The
[physical strict audit](../../../../../Physics/FieldTheory/Jets/Weyl/Equations/Audit/AuditWeylJetAdjoint.lean)
checks all 72 new physical declarations and their dependencies.

## Free Abelian Field-Strength Jets

The [Abelian field-strength dossier](../../core/Physics/ABELIAN_FIELD_STRENGTH_IBP.md)
uses one complexified free source-free bosonic field strength, four ordinary
commuting derivative labels, signature (+---) and the existing actual Pauli
SL(2,ℂ) vector/dual-direction actions. The ordered-pair tensor source has
explicit algebraic antisymmetry and diagonal relations. The Maxwell and cyclic
Bianchi seeds, their equation parameter representations and actual covariance
are constructed. Metric intertwining follows from the proved quadratic
invariance; no physical equation covariance or rank premise is assumed.

The full polynomial-descendant closure gives commuting quotient shifts and
the actual group action. The component wave equation and all its descendants
follow from antisymmetry, Maxwell and Bianchi. Two transverse null-symbol probes
annihilate the entire relation module and detect independent arbitrarily high
jets. Nonzero controls persist in the symmetric and common even algebras before
IBP, without a physical helicity-count or integrated-invariant conclusion.

The actual onto projection has the proved descendant-ideal kernel presentation.
Finite image grades, derivative compatibility and inverse equivariant EOM/IBP
source and coefficient descent are instantiated from the common linear package.
An empty odd species set introduces no odd field or equation premise. IBP stays
a linear divergence range. The
[persistent strict audit](../../../../../Physics/FieldTheory/Jets/Gauge/Audit/AuditMaxwellLinearEquation.lean)
checks the physical interface and transitive dependencies with the standard
axioms only. Potentials/gauge exactness, analytic Physlib equivalence, matter
sources, non-Abelian interactions, Hodge/helicity classification, amplitudes,
matching and rates remain outside this source model.

## Polynomial Scalar EOM And Formal Matrix Yang–Mills

The [formal interaction dossier](../../core/Physics/FORMAL_YANG_MILLS_IBP.md)
specifies a neutral complexified scalar equation `box phi + lambda * phi^3`
on the existing four-dimensional jets with signature (+---). The actual Pauli
SL(2,ℂ) action fixes the seed and preserves its entire differential ideal;
Lorentz transport on the EOM algebra and linear EOM/IBP source is constructed.
The retained current proves `kinetic = lambda * phi^4` modulo EOM and IBP.
Neither integrated class is asserted nonzero. Zero-field evaluation detects
the surviving unit in the EOM algebra. No variational derivation is assumed.

The formal matrix consumer uses arbitrary finite decidable matrix indices,
with every connection entry and its ordinary derivatives as actual bosonic
polynomial variables. Associative curvature and covariant derivatives give
`E_nu = sum_mu s_mu * nabla_mu F_mu,nu`, with signature (+---). The equation
entries generate the full differential ideal; ordinary and covariant EOM
descendants vanish. Curvature commutators and Bianchi are proved off shell.
The actual onto/kernel, finite image and inverse EOM/IBP interfaces apply.
Zero-field evaluation proves that the EOM algebra is nonzero; a two-by-two
constant-jet evaluation detects a nonzero nonlinear off-shell EOM component
that is killed by the projection.

This is an associative complex matrix model, without SU(N) real/traceless
conditions, arbitrary local gauge covariance, an analytic Yang–Mills or
matrix-model Lorentz dictionary, mixed nonlinear fermion equations, general
operator counts, amplitudes, matching, RGE or numerical dynamics. The
[strict physical audit](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditNonlinearGaugeJets.lean)
checks all 74 new public physical declarations transitively, rejects GUT
imports and permits only the standard axioms. Tong's formulas guide conventions
and supply no external theorem premise.

## Internal-Unit Yang–Mills Covariance And Complete Scalar Degree Two

The [gauge/trace and scalar degree dossier](../../core/Physics/GAUGE_TRACE_SCALAR_DEGREE.md)
specializes internal-unit transformations to the actual formal matrix jet
connection. Curvature and signed EOM conjugation are proved. Transformed
equation entries lie in the original full EOM ideal and vanish on shell.
Traces of squared curvature components are invariant; trace covariant IBP
descends through the actual ordinary divergence range.

The actual connection/curvature/Yang–Mills equation have engineering degrees
one/two/three. The interacting scalar seed has degree three for arbitrary
complex coupling. These statements use the constructed weighted sources,
without assuming a global on-shell grading.

For one neutral scalar in four directions, the degree-two image in the full
unbounded EOM/IBP source has basis the field square and dimension one for
every complex coupling. Complete monomial reconstruction covers the square
and four first jets; the latter are divergences. A polynomial evaluation maps
the entire EOM ideal into `(t^3)`, while all derivatives evaluate to zero.
Its `t^2` coefficient functional annihilates all EOM and IBP relations and
detects the square with value one. No degree truncation of relations or
external completeness/rank matrix is used.

The [physical audit](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditGaugeEngineering.lean)
checks all 40 named public declarations transitively under the existing
standard-axiom/import policy. The result does not construct a local gauge
orbit quotient, SU(N) real/traceless conditions, a matrix-model Lorentz
dictionary or general invariant counts. Lagrangian and formal first-variation
derivations remain deferred, with analytic dynamics and phenomenology outside
scope.

## Local Polynomial Lagrangian Helper

The [helper consumer](../../../../topics/local-lagrangian-helper/results.md)
reuses the existing actual Lorentz scalar field and four ordinary directions,
signature (+---) and arbitrary complex coupling g. Its generated equation for
the kinetic density plus `-g*phi^6/6` is `-(box phi + g*phi^5)`. The source
action, generated differential ideal stability and actual divergence
covariance are proved; the packaged caller supplies only g. Coefficient
operations use the existing common derivative input. This bounded consumer
does not infer invariance of arbitrary new interactions or provide a real
action/analytic variational principle. The general mixed example is algebraic
and does not supply a physical spinor/gauge contraction dictionary.

## Formal First Variation

The [formal first-variation result](../../../../topics/formal-first-variation/results.md)
uses complex polynomial jets in four commuting ordinary directions. Arbitrary
polynomial variations are prolonged to every jet. Finite matrix indices,
commutative complex coefficient algebras and explicit commuting derivations
support the trace identity. The scalar coupling is arbitrary complex; the
physical consumers use signature (+---). Normalized Euler coefficients and
all descendant ideals are proved to agree with the existing EOM inputs,
including the matrix transpose and signature signs. No analytic action,
boundary condition, literature identity or quantum equivalence is assumed.

## Additive Derivative Input Adapters

The [adapter result](../../../../topics/derivative-interface-adapters/results.md)
preserves the published nonderivative source/API. A proved coefficient
presentation and its explicit input evaluation law transport additional stable
source relations to their actual coordinate images. Finite local coordinates
retain normalization, invariant completeness and exchange hypotheses; no
flavor-dimension, averaging or invariant-complement assumption is added.
The new source-map adapters use additive-group complex modules.
Actual direction-covariant mixed divergence and equivariant zero-jet bridges
are reused. Full polynomial EOM inputs require annihilation of the complete
differential ideal and divergence range and combined residual stability;
they assume no homogeneous shell decomposition. The scalar consumer proves
that stability for the existing actual Lorentz action and retains the
cross-grade interaction equation. No new literature, analytic action,
Lagrangian input or quantum premise is introduced.

The uniform `Math.MixedOperatorInput` entry accepts natural-number derivative
degrees including zero. Its actual source/action includes arbitrary supplied
field and direction representations, with finite direction index type. The
IBP relation is bottom at zero and the actual divergence range at positive
degree. The original zero-order exterior/symmetric source is equivariantly
recovered even with direction mixing; existing nonderivative callers gain no
new hypotheses. This grading is an off-shell/IBP interface, not an assumed
grading of the nonlinear EOM quotient.

The optional `Math.DerivativeInterface.Input` record packages source action,
actual relation module and stability, with separate graded and commutative
EOM factories and common coefficient operations. Configuration hypotheses are
unchanged. For a supplied invariant subspace, selection uses the preimage of
the complete relation module and has a proved linear equivalence to its image
in the full quotient. Global coefficient restriction is compatible; extension
of all selected invariant coefficients is not asserted. The actual Lorentz
scalar factory packages its existing covariance, and its invariant wave/cubic
selection retains the cross-degree EOM law. No global decomposition, finite
dimension or invariant-complement premise is introduced.


## Registered Lagrangian Models And Scalar/Weyl Yukawa

The [registered entries](../../../../topics/lagrangian-model-connections/input-guide.md)
reuse checked scalar/Higgs densities and actions with unchanged input types.
The [Yukawa input](SCALAR_WEYL_YUKAWA.md) adds the complete scalar/paired-Weyl
kinetic, mass and interaction density on four ordinary directions, with actual
SL(2,C) and independent complexified conjugate labels. One even component is
the scalar; three unused even components have zero EOM. Couplings can vanish.
Full relation stability follows from proved Euler covariance; density symmetry
is checked independently. The specified DHM component dictionary relates the
printed contractions and kinetic to this algebraic source. No reality quotient,
local gauge field, quantization, rate or finite universal solver is assumed.


The [automatic Yukawa connection](../../../../../Physics/FieldTheory/Jets/Lagrangian/EulerDensityConnection.lean)
uses the independent total-density invariance theorem and the general linear
Euler-naturality constructor. Its model equals the previous independently
certified model. The existing complexified-component, local-algebra and
reality/gauge boundaries remain unchanged.
