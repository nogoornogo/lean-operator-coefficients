# Outside-Family Trials of the Content Adapter

## Results

All trials use the actual three-generation signed SM/Weyl fields, universal
physical cyclic charges (q,q,q,l,l), positive cyclic order k, and neutral
one-copy Higgs/dual fields. They are constructed contents, not new UV models.

| Content | Charges and count filter | Result in the whole selected actual space |
|---|---|---|
| No fermions, pure Higgs/dual fields | Y=0, c=0 | Allowance iff h=a; actual empty-degree seed constructed |
| Three Q fields | Y=3, c=3q; arithmetic permits a=h+1 and 3q=0 | Forbidden for every h,a by odd fermion degree, including neutral q=0 |
| Two physical uR and four physical dR | Y=0, c=6q | Allowance iff h=a and 6q=0; the subsequent actual seed connection is proved |
| Two L fields, previous comparison | Y=-6, c=2l | Allowance iff h=a+2 and 2l=0 by the subsequent Higgs-containing seed connection |

[OutsideFamilyHiggsTrials](../../../Physics/StandardModel/Operators/OutsideFamilyHiggsTrials.lean)
contains the first three trials. The LL comparison reuses
[ContentHiggsSupport](../../../Physics/StandardModel/Operators/ContentHiggsSupport.lean).

## Positive control and arithmetic failure

The pure-scalar case tests the generic constructor outside the four families.
emptyCoefficient descends the constant alternating map at exterior degree zero
and is actually invariant and nonzero. Its supported seed satisfies the
adapter premise; scalar_only_allowed_iff classifies the whole scalar content.
This is a boundary/control case with no fermions, not a new positive result
for a different nonzero fermion number or a certificate of invariant-ring generation.

tripleQ_forbidden applies the actual odd-degree theorem. The explicit
neutral_arithmetic_not_sufficient example takes q=0 and (h,a)=(0,1), where
both charge/count equations hold, but every coefficient vanishes. Therefore
the necessary filters alone cannot justify the seed premise. A raw three-Q
content is not a Lorentz scalar even if hypercharge is compensated by a dual Higgs.

## Six-quark trial at checkpoint 01

sixQuarks is a permutation orbit of the actual signed species pattern
(1,1,2,2,2,2), meaning physical uR squared times dR to the fourth power.
six_stable proves it is a valid permutation-stable content. Its hypercharge
and residual charge are derived from those labels rather than assumed.
The generic adapter proves six_necessary and six_obstructed, at arbitrary
Higgs count. six_iff_of_seed is explicitly conditional on a nonzero supported
actual exterior-six coefficient when 6q=0.

The inspected six-quark assets provide typed flavored tensors, local invariance,
species alternation and residual coordinates. GradedSixQuarkComparison
connects a specified two-species input to its quotient. It does not by that
statement identify a supported exterior coefficient in the ten-species
signed-field carrier used here. This trial does not treat a neutral ordered
tensor or its coordinate count as a witness in SeedSpace.

To discharge the premise, transport the existing actual statistical six-quark
coefficient through a proved species/field dictionary into that SeedSpace,
and prove a nonzero witness under the present three-generation cyclic action.
That transport was not proved at the bounded trial checkpoint; no full six-quark iff
or all-Higgs allowance is claimed. The diagnostic identifies a specific
connection task rather than an invariant-theory foundation or a new axiom.

## Scope

The [trial contract](outside-family-contract.md) is reached: one positive
constructor control, a certified neutral-arithmetic rejection, and a real
six-fermion input with certified necessary filters and an identified seed gap.
The four-family theorems, finite candidate counts and broader support boundary
remain unchanged. No new finite generating family, VEV, mass, anomaly, UV
realization, amplitude or rate is inferred. See [verification](verification.md).

## Subsequent connection completed

[SixQuarkFullSeed](six-seed-results.md) now proves the previously missing
actual supported exterior seed and its nonzero transport. Whole-content
allowance iff h=a and 6q=0 is established. The preceding discussion records
the original trial boundary rather than a remaining seed obligation.

## LL comparison subsequently completed

[LLHH connection](llhh-results.md) now proves the LL whole-content iff,
using the actual Weinberg seed and symmetric coefficient multiplication
rather than the zero-Higgs constructor.
