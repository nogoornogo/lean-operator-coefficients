# Actual Exotic Copies: Arbitrary-Mass Bounds and SM Exclusion

This completes the first endpoint in [the mass plan](exotic-mass-plan.md).
The wider family containing 10/bar10 and bar5/5 is not excluded by this result.

## Fixed actual input family

Let S(p,s) be p copies of the actual chosen 40 and s copies of the actual 50.
The original field representation is S(p,s) plus the algebraic dual of S(q,t).
Thus both conjugate orientations and arbitrary natural copy counts occur.
The action is the standard SM covering action, with no extra residual symmetry.
The mass B is any invariant symmetric complex bilinear form on this entire
representation, including arbitrary mixing. No rank, matrix entries or VEV
are prescribed. The light fields are its actual radical.

[ActualExoticMassBounds](../../../GUT/SU5/SelectionRules/ActualExoticMassBounds.lean)
constructs this family from the actual kernel representations. Let mQ and mU
denote their proved positive full-SM Hom multiplicities in one 40. They are
not replaced by the unproved numerical values one.

## Every invariant mass

| Selected species | Source Hom dimension | Mass-target Hom dimension | Proved light lower bound |
| --- | --- | --- | --- |
| Q | p mQ | q mQ | max(p-q,0) mQ |
| uc | p mU | q mU | max(p-q,0) mU |
| ec | 0 | Not needed | Exactly zero |

The first two bounds are `arbitrary_mass_lower_bounds`. In particular, p>q
forces nonzero Q and uc maps into the actual radical for every B, regardless
of s and t. The 50 copies supply no selected Q/uc partners. The necessary
conditions `no_light_q_necessary` and `no_light_u_necessary` say p<=q if all
maps of the respective selected species into the radical vanish.

These are conditions for eliminating a species. They are not conditions for
forbidding all Delta B=1 operators. An SM spectrum itself requires Q and uc;
the existence of these two species alone does not prove nonzero qque.

## An actual SM obstruction

`arbitrary_mass_no_electron` proves every ec map into the radical is zero,
for all p,s,q,t and all B. This includes the conjugate sectors, whose absence
follows from the previously proved same-orientation pairing exclusions.
Mass removal cannot create a species absent in the original representation.

`no_exact_sm_light` proves that the radical cannot be equivariantly equivalent
to N copies of the usual five SM fermion species for any positive N. Its
target explicitly includes Q, uc, ec, dc and L with their actual gauge actions,
not just charges or dimensions. The proof transports the target's electron
inclusion back to the actual radical and contradicts the preceding zero theorem.
More generally any target admitting a nonzero ec map is impossible here.

Consequently the exotic-only 40/50 family has no exact SM light realization.
This excludes that input family by SM compatibility, not by a new proton
protection no-go. Adding 10, for example, changes the family and supplies ec;
the exclusion must not be applied to that larger input space.

## Reusable mass interface

[HomSurplusMass](../../../Physics/FieldTheory/Mass/HomSurplusMass.lean)
connects actual source/partner Hom multiplicities directly to the original
mass radical. Existing `SpeciesCopySurplus.homKernelEquiv` and rank-nullity
give the bound. No full spectator decomposition, semisimple splitting,
irreducibility or supplied `SpeciesSectorPresentation` is needed.
No-pairing premises at this generic layer are proved for the concrete family
by the actual 40/50 theorems. The application does not assume formal profiles.

## Remaining full-family connection

The subsequent [full-family result](full-family-results.md) closes the actual
index and coefficient connection for the declared gauge-only, exact-SM class.
The following paragraphs record the prerequisite boundary at this earlier
checkpoint; a full color/weak branching equivalence is still not claimed.

The family with 10/bar10 and bar5/5 is still open. Its source contains ec and
the above SM contradiction no longer applies. Prior formal four-row index
constraints remain separate from this actual family theorem. Complete
spectator index evidence (or an equivalent actual-character extraction),
the connection of an SM-only light target to those UV indices, and the
physical coefficient endpoint still require proof.

The new Hom interface removes the need to manufacture a full mass-sector
presentation merely to obtain a selected-species survival bound. It does
not prove the remaining spectator or SM-only premises. Exact Q/uc one-copy
counts are also still open. No protecting model or exhaustive exclusion of
the larger family is claimed. See [verification](verification.md).
