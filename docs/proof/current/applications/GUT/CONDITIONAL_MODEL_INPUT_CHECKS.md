# Conditional model-input consumers

The [topic result](../../../../topics/conditional-model-input-check/results.md)
separates ten candidate groups, successful restricted inputs and unresolved
model correspondence. These consumers apply existing coefficient theorems;
they do not derive UV spectra, stabilizers, light-field maps or matching.
Every minimum here is a **derivative-free** engineering-dimension minimum
within the declared fixed SM/Higgs domain. Covariant derivatives, EOM/IBP
quotients and generated interactions are not certified. See the
[current scope map](../../RESULTS_AND_SCOPE.md).

## Neutral-Higgs SM inputs

[ConditionalInputChecks](../../../../../GUT/Common/ProtonProtection/ConditionalInputChecks.lean)
uses fixed ten signed three-generation SM fermions, one neutral-residual Higgs
and its dual, independent Lorentz symmetry and derivative-free coefficients.
Physical right-handed conventions are used before signed opposites are formed.

For q=2,l=0 modulo 18, `dfpw_b1_forbidden` proves OriginalForbidden for
absolute 3B=3 at every content and Higgs bidegree. `dfpw_six_forbidden`
proves full uR²dR⁴ content vanishing at every Higgs count. These are conditional
consumers of the supplied DFPW subgroup dictionary, not UV spectrum proofs.

`lepton_parity_b1_forbidden` proves the absolute all-degree B1 statement for
q=0,l=1 modulo two. The two named allowance consumers retain the distinction
between B1 prohibition and selected six-quark/LLHH allowance.

`trivial_b1_minimum` proves IsMinimum (0,0 mod 2) 3 12. The grade is twice
the canonical dimension. `matter_parity_b1_minimum` proves the same minimum
for (1,-3 mod 6), with separate actual six-quark and LLHH allowance witnesses.
For (1,-3 mod 5), the selected contents are forbidden at every Higgs count;
`bl_subgroup_b1_minimum` concerns only this subgroup's permission.
`sm_even_weinberg_allowed` supplies the SM-even LLHH consumer.
The original coefficient minima and content equivalences supply these results;
finite charge neutrality is never treated as sufficient by itself.

## Charged-Higgs restriction

[BaryonTrialitySMInput](../../../../../Physics/StandardModel/Operators/BaryonTrialitySMInput.lean)
proves actual scalar actions, a nonzero-value charge constraint and 9-divisibility
of 3B. It uses local hypercharge neutrality and an explicit integral charge
identity. `all_forbidden` eliminates absolute B1/B2 at every mixed degree on
arbitrary complex copy modules; `residual_forbidden` uses the existing composed
coefficient equivalence. The component dictionary matches the declared source
convention modulo three. No SUSY operator alphabet is constructed.

`proton_hexality_inverse_dictionary` checks component agreement with the existing
BGW dictionary modulo six after generator inversion. This justifies reuse of
BGW on that normalized component input, conditional on its supplied identification
with the literature model's selected SM fields. No full FN model is certified.

## Trust and verification

[AuditConditionalInputChecks](../../../../../GUT/Common/ProtonProtection/Audit/AuditConditionalInputChecks.lean)
checks every new named declaration plus selected reused simultaneous/model
certificates transitively, allowing only propext, Classical.choice and Quot.sound.
See the [source register](../../../../topics/conditional-model-input-check/sources.md)
and [verification](../../../../topics/conditional-model-input-check/verification.md).

## Explicit B-L / LR action bridges

The [continuation](../../../../topics/conditional-model-input-check/bl-lr-results.md)
adds `BLResidualRestriction`: the Z6 embedding is injective and its image is
exactly the charge-six nonzero-VEV stabilizer in Circle. Constructed continuous
SM flavor actions restrict to the q/l input; the equality includes actual
signed gauge/Weyl fields and neutral Higgs/dual fields. B1 minimum attainment
and the lower bound are stated on the restricted continuous action itself.

`LRLightHiggs` constructs the neutral LR bidoublet, its SM restriction and the
positive-column inclusion/retraction. A supplied diagonal quadratic operator
with nonzero heavy and zero light eigenvalues has precisely that doublet as
its kernel. The complete kernel representation and dual are identified with
BnvMixedInput.scalarGauge 0/1; the action agrees with actual bidoublet restriction.
This is conditional scalar selection, not a derived LR potential, generic
Higgs mixing, global quotient or fermion-spectrum result.

## Model-admission premise controls

The [source-specific recheck](../../../../topics/conditional-model-input-check/model-admission-results.md)
keeps candidate 8's scalar-selection premise explicitly unverified.
`LRModelAdmissionControls` proves the (1,1) quadratic operator is the identity
with zero kernel, the (0,0) operator has the entire bidoublet kernel, and the
(1,0) operator has the selected Higgs kernel. The identity is even full-LR
equivariant. Thus representation invariance alone is insufficient to infer
single-Higgs selection. No complete potential or source-model counterexample
is constructed. Candidate 7's checked action correspondence likewise does not
prove a UV sterile/light mass-radical identification.
