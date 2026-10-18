# Actual Six-Quark Seed: Connection Completed

## Exact result

For the actual three-generation signed SM/Weyl input with universal physical
cyclic charges (q,q,q,l,l), positive cyclic order k and neutral one-copy
Higgs/dual fields, the whole physical uR²dR⁴ content satisfies

    allowance iff h=a and 6q=0 mod k,
    prohibition iff h!=a or 6q!=0 mod k,
    prohibition at every Higgs count iff 6q!=0 mod k.

The actual supported nonzero exterior-six seed is now constructed when 6q=0.
The conditional premise of the previous six_iff_of_seed consumer is discharged.
No individual neutrality q=0 is required. The result does not classify every
B2 fermion content, its coefficient basis or UV generation.

## Actual connection

[SixQuarkFullSeed](../../../Physics/StandardModel/Operators/SixQuarkFullSeed.lean)
uses SixQuarkTwoCoordinates.twoCoordinateEquiv to construct an actual nonzero
degree-(2,4) invariant exterior coefficient on Quark x Quark. This source
already includes species statistics and physical gauge/right-Weyl invariance;
it is not a neutral ordered-tensor ansatz.

strip evaluates the flavor factor at coordinate zero on the actual up/down
field carriers. projection takes species 1 and 2 from the ten-species field
sum and strips their flavor factors. inclusion embeds both quark components
with a constant flavor vector, and projection_inclusion proves a right inverse.
This certifies preservation of nonzero coefficients upon pullback.

strip_up_action and strip_down_action identify the projected actual actions
with the existing physical upField/downField actions times the common cyclic
phase. projection_action combines those statements. The exterior degree-six
phase equals one when 6q=0, so raw is an actual invariant coefficient for the
entire gauge/Lorentz/cyclic input. raw_nonzero follows from the right inverse
and the constructed localSeed, with no nonzero premise supplied externally.

## Support and all-Higgs transport

support_of_nonzero proves that a nonzero pure-species value can contain only
up and down fields: projection annihilates every other species. Actual
hypercharge invariance then forces exactly two up and four down slots. The
finite cardinality proof and permutation_of_counts put those labels in the
selected sixQuarks orbit. Thus seed belongs to ContentHiggsSupport.SeedSpace,
not only the ambient exterior coefficient space.

seed_exists is the actual witness required by the generic support adapter.
Its proved balanced dressing then supplies the sufficient direction at every
Higgs count; the earlier hypercharge/residual obstruction gives necessity.
The full selected coefficient space is still defined independently of this
witness. No assertion that all coefficients are such dressings is made.

## Scope and verification

The [contract](six-seed-contract.md) is complete. This closes the exact field,
statistics, support and nonzero bridge identified by the
[outside-family trial](outside-family-results.md). The old conditional theorem
is preserved as a reusable consumer; the new allowed_iff and
all_forbidden_iff are unconditional under the fixed physical input above.

The finite covariant generation theorem, other contents and complete
all-degree B1/B2 support remain open. No VEV, mass, semisimplicity, anomaly,
UV lift, matching, amplitude, rate or literature premise was added. Candidate
counts are unchanged. [Verification](verification.md) records strict audits,
focused/full builds and layout/document checks. No master merge or push was done.
