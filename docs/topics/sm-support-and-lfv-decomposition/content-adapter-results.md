# Generic Content Support and Its Exceptions

## Actual-carrier API

[ContentHiggsSupport](../../../Physics/StandardModel/Operators/ContentHiggsSupport.lean)
accepts an arbitrary fermion degree n and a content predicate P on species
labels in the actual three-generation signed SM/Weyl alphabet. The residual
input remains universal physical cyclic charges (q,q,q,l,l), positive cyclic
order k and neutral one-copy Higgs/dual fields. Space is the whole selected
actual coefficient subspace, defined independently of seeds.

The selected_stable theorem transports a supplied permutation-stability proof
to mixed support. The obstruction and witness arguments themselves do not
need stability as an extra hypothesis: they use the already alternating and
symmetric actual carriers. Stable predicates remain the intended content inputs.

Supply certificates that selected labels have constant fermion hypercharge Y
and constant residual charge c. The necessary theorem proves

    allowance implies Y+3h-3a=0 and c=0.

This is a necessary condition without a support-existence assumption. In
particular, if 3 does not divide Y, the content is forbidden at every Higgs
count. Odd fermion degree, or degree above the proved three-generation bound
180, also makes every selected coefficient zero. These are actual exclusions,
not conclusions inferred from a missing certificate.

## Neutral-hypercharge constructor

For Y=0, a supported zero-Higgs exterior coefficient belongs to SeedSpace.
The adapter needs a proof that c=0 implies an actual nonzero element of this
space. It constructs the scalar dressing and proves support and nonzero
membership at every balanced count, deriving

    allowance iff h=a and c=0,
    all-Higgs prohibition iff c!=0.

The seed premise is explicit, not an axiom or a newly proved existence theorem
for all contents. Dressing support and nonzero preservation are proved inside
the adapter, rather than supplied as additional assumptions. No finite
covariant spanning premise is used. The total charge c need not be 3q+l.

family_seed discharges the premise for every DUQL/QQUE/QQQL/DUUE instance
through the already certified statistics-aware dictionary. family_control
identifies the selected space with FourFamilyHiggsContent, and
family_allowed_iff recovers its complete fixed-content iff by the new API.
Thus the adapter has four actual consumers, not only a conditional statement.

## How to separate other inputs

| Input property or gap | Certified consequence or next obligation |
|---|---|
| Y=0, constant c, neutral seed proved | Exact whole-content support via the adapter |
| Y!=0 and divisible by 3 | Necessary shifted count relation h-a=-Y/3; construct a Higgs-containing seed and certify its propagation before asserting sufficiency |
| Y not divisible by 3 | All Higgs counts excluded |
| Odd fermion degree | Actual Lorentz/exterior coefficients vanish for all Higgs counts |
| Fermion degree above 180 | Actual exterior source is zero, for all Higgs counts |
| Constant c not established | Prove the scalar charge action or decompose into residual components; this diagonal cyclic adapter alone does not cover arbitrary actions |
| Y=0 and c=0, but neutral seed not proved | Undetermined support; inspect gauge/Lorentz/statistics or construct an actual seed |
| Zero-Higgs seed absent | Does not by itself rule out Higgs-dependent operators |

This is a map of proof obligations, not a disjoint exhaustive model partition.
Properties can overlap. Passing the numerical conditions is not a realization
certificate. The final two rows must not be treated as no-go evidence.

## Initial shifted-content control

leptonPair selects two physical L fields. Its actual charges are Y=-6 and
c=2l. The API proves

    allowance implies h=a+2 and 2l=0.

Every balanced h=a coefficient in this content is zero. This explicitly
shows why the four-family balance rule cannot be extended to all inputs.
No sufficiency or new LLHH coefficient dictionary is claimed by this control;
connecting a Higgs-containing seed is the remaining positive-direction task.
The existing separate Weinberg results are not silently imported as a match.

## Endpoint and boundary

The [contract](content-adapter-contract.md) is achieved: actual generic
obstructions and neutral-seed dressing, four discharged consumers, and
shifted/parity/degree controls. This does not classify the finite fermion
universe, prove covariant finite generation or start arbitrary nonabelian
B1 support classification. The earlier 572 assignments/151 orbits are unchanged.

[Verification](verification.md) records focused and full builds, strict audits
and layout/document checks. No new dependency, heartbeat, literature axiom,
physical premise, UV model, amplitude or rate was introduced. No master merge
or push was performed.

## LL shifted seed subsequently connected

[WeinbergFullSeed](llhh-results.md) now discharges the LL Higgs-containing
seed connection and proves the stronger whole-content iff at every scalar
count. The initial necessary-only control above remains a valid theorem;
its sufficient-direction gap is closed by the separate actual construction.
