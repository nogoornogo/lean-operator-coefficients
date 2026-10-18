# Excluding Unsuitable Residual Actions Before Model Construction

## Output and exact scope

[ResidualQquePrefilter](../../../Physics/StandardModel/Operators/ResidualQquePrefilter.lean)
adds a necessary-condition filter on Abelian residual actions commuting with
the standard SM covering group. It uses the existing physical neutral-qque
exterior theorem; it does not discover a new independent obstruction.
The new interface applies that obstruction to actual invariant light
subspaces, indexed parameter families and the previous actual UV copy filter.

An admitted `Triplet` contains actual Q, uc and ec invariant subspaces of
one SM x H light representation, with equivariant identifications with
character-twisted SM species. These identifications include both gauge and
residual actions. The right-handed coefficient carriers are the algebraic
duals of uc and ec; the adapter proves the required charged bidual transport.
A numerical spectrum or list of charge labels does not supply this dictionary.

If prohibition covers every admitted triplet, then on each triplet

    chi_Q^2 * chi_uc^(-1) * chi_ec^(-1) != 1.

This is nontriviality as a character of the whole residual group, not merely
at one chosen element. If the character is trivial, an explicitly nonzero
fermionic exterior qque coefficient exists on those actual subspaces and
`neutral_excludes` rejects that action. A full B1 prohibition covering these
carriers therefore cannot hold. No generated coupling or decay rate follows.

## Excluded action patterns

| Certified pattern on an actual admitted triplet | Result |
| --- | --- |
| All three species have the same residual character | `equal_species_excludes` rejects protection |
| Q=a*c*w, uc=a*c*c, ec=a*w*w pointwise | `block_excludes` rejects protection |
| Any other action with trivial qque character | `neutral_excludes` rejects protection |

The block factors need not be characters; the species charges must be genuine
characters. These patterns can overlap. Equal charges include a trivial
residual action but are not restricted to it. The result is independent of
generation count and of whether a chosen mass is maximal rank.

`selectedTriplet` constructs actual invariant ranges in an explicit product
of the three charged species; `selected_neutral_reject` is a nonvacuous
regression. This selected-species action is not a full SM spectrum or UV model.

`uniformSM_gauge` and `uniformSM_reject` additionally give a complete
one-generation SM control: a common residual character twists the actual
restricted 10 plus bar5, so the gauge restriction remains exactly the SM
generation. Actual Q/uc/ec ranges are constructed from its existing branching
maps, and protection is rejected for every such character. This shows the
residual test can reject an SM-compatible light action, rather than merely a
three-species charge table. No UV lift, anomaly or mass-generation claim is
inferred from this control.

## Combined input filter

[FullFamilyResidualPrefilter](../../../GUT/SU5/SelectionRules/FullFamilyResidualPrefilter.lean)
accepts an explicit gauge-restriction equivalence between the SM x H light
action and the unchanged radical of the original invariant symmetric mass.
An exact N-generation SM equivalence is supplied for that gauge restriction.
For the actual 10/bar5/40/50 plus conjugate-copy family, protection requires
both the previous net-copy constraints (N,N,0,0) and the nontrivial-character
condition on every admitted triplet. Thus an input passing the SM copy filter
can still be rejected by a neutral residual carrier, before matching.
`joint_reject` rejects the joint SM/prohibition request when either necessary
copy or residual condition fails.

The combined theorem requires that bridge rather than assuming the residual
action exists on a radical from its charge table. It does not prove a residual
UV lift, an additional symmetry of the original mass, or a scalar/VEV realization.

For symbolic parameters, `preserve` proves that genuinely protected inputs
satisfying the declared SM condition survive `retain`. A supplied indexed
list of actual triplets gives `selectedRetain`; `finiteCandidates` and
`finite_preserve` permit a finite parameter filter with a separately supplied
decision procedure. No exhaustive physical parameter catalogue or executable
character-equality procedure is inferred from these definitions.

## Limits and stopping point

Passing this filter is not a proof of protection: mixed pairs of different
Q characters, other qque carriers and other B1 operators may still be allowed.
If no dictionary is constructed, the test may be vacuous; this is unknown
coverage, not a protection certificate. A prohibition domain omitting the
witness carriers is outside the exclusion. Non-Abelian and noncommuting
residual actions are not treated by this scalar-character interface.

The declared interface endpoint is complete. Applying it to a new concrete
UV family requires proving its actual light subspace/character dictionary;
that work is not replaced by this filter. No new model enumeration or new
physical no-go class is claimed. See [verification](verification.md).
