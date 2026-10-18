# B-L and LR action/selected-Higgs bridges

This continuation follows the [frozen plan](bl-lr-plan.md) on the same topic
branch. The original ten-candidate review remains a separate verification
baseline. The source conventions are unchanged in [the register](sources.md).

## B-L residual restriction

[BLResidualRestriction](../../../GUT/Common/ProtonProtection/BLResidualRestriction.lean)
constructs the injective homomorphism from Multiplicative(ZMod 6) to Circle
using ZMod.toCircle. `range_iff` proves that its image is exactly z^6=1.
`vev_stabilizer` proves that this image is exactly the stabilizer of any nonzero
complex charge-six VEV. Thus subgroup membership and the absence of additional
pure-X stabilizers are proved, not inferred from counting sampled phases.
`negative_vev_fixed` also checks the charge-minus-six VEV of the LR convention.
This concerns the X=3(B-L) Circle factor, not the full LR stabilizer or a
faithful quotient by gauge centers.

For every one of the ten signed physical SM species, `charge` is 3B-3L,
where the stored baryon grading is already 3B. Opposite species carry opposite
charges. `uvFlavor` constructs the continuous action on three generations;
`flavor_restriction` identifies its cyclic restriction with the exact
QLFiniteSupport dictionary (q,l)=(1,-3 mod 6). `actual_field_restriction`
extends this equality to the actual SM gauge/Weyl tensor fields. Both Higgs
and dual field actions are neutral and have actual restriction identities.

`restricted_b1_attained` and `restricted_b1_lower` state the attained minimum
grade 12 (physical dimension six) on this restricted continuous-action input
itself, using the existing general minima theorem. This is permission for the
restricted action; a subgroup witness is not asserted to be a full continuous
B-L invariant. The correspondence no longer consists of a charge table alone.

The continuous SM representations are explicitly constructed from the stated
charges. Their identification with a particular UV mass radical is still a
model input: neither light-generation counting nor the sterile-neutrino mass
spectrum follows from a residual-action identity.

## LR bidoublet and one selected light Higgs

[LRLightHiggs](../../../GUT/Common/ProtonProtection/LRLightHiggs.lean) constructs
SU2_L × SU2_R × Circle_X and its neutral bidoublet representation. The
SM-cover homomorphism uses the existing right-handed torus and weak action;
`restriction_eq` connects it to the existing independently checked Hom(right,left)
bidoublet decomposition. The unused SU4 factor in that construction has no
bidoublet action; no PS mass or matching premise is imported.

The two columns have 6Y=-3,+3. `includeHiggs` embeds the positive column and
`projectHiggs` retracts it. `include_equivariant` identifies the domain with
BnvMixedInput.scalarGauge 0, the actual standard SM Higgs representation.
The pure-X residual subgroup acts trivially on the entire bidoublet.

The explicit quadratic operator has column eigenvalues (heavy,light).
`quadratic_equivariant` proves SM covariance. For nonzero heavy and light=0,
`kernel_eq_range` proves that the whole kernel is exactly the positive-column
image. `kernel_of_coordinates` states the same result for an arbitrary supplied
linear operator M satisfying the displayed coordinate action. The hypothesis
is a theorem parameter, not a derived property of a UV potential. A positive
real heavy parameter is included as a special case.

`lightEquiv` identifies the complete selected kernel with one doublet.
`lightRepresentationEquiv` and `light_action` prove that the transported kernel
action is the restriction of the actual bidoublet SM action and equals the
standard Higgs representation. `dualLightRepresentationEquiv` supplies the
existing dual-Higgs convention. `light_residual_action` proves residual
neutrality on this kernel. These are complete representation identifications
for the specified selection, not just an invariant vector construction.

## Exact remaining boundary and stopping decision

Both planned algebraic bridges are complete. The missing single-doublet
identification has been replaced by an explicit map and a conditional complete
kernel theorem. It has not been replaced by an unproved assertion that the
literature model's scalar potential realizes these eigenvalues.

Still external: the particular LR potential/parameters yielding the coordinate
hypothesis, a generic conjugate-column mixture, full multi-Higgs physics,
fermion UV mass-radical identifications, faithful global quotient and full LR
vacuum/stabilizer. No anomaly, UV completion, EWSB, matching or rate theorem is
claimed. No new foundation or dependency was needed. The source default
heartbeat limits and existing resource guards remain unchanged.

See [continuation verification](bl-lr-verification.md). Completion and the
verified topic commit do not authorize master integration.
