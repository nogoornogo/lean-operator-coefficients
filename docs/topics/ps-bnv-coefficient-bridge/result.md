# Exact Conditional Coefficient Result And Bounded Stop

The specified component mechanism now has a Lean certificate beyond symmetry
permission: a signed scalar-source action is eliminated, its result is admitted
to the actual dimension-seven SM/Lorentz exterior coefficient sector, and its
EW-substituted image is nonzero on specified light fields. This is conditional
on the supplied PS component/Yukawa dictionary, selected effective Higgs
direction and UV C_L,C_R. It is not a
full PS representation adapter or a proton-decay-rate theorem.

The planned fully normalized comparison to the pinned paper stops at the
[source normalization boundary](conventions.md#normalization-boundary-in-the-pinned-source).
No leading-order finite-mu formula or unchecked normalization is promoted to
an exact physical matching theorem.

## Proved Chain

1. [UVComponent](../../../GUT/PatiSalam/Matching/UVComponent.lean) proves the
   epsilon component factor four and the covariant identical-Q factor two.
   This is a selected finite contraction check, not full PS operator completeness.
2. [TwoSourceQuadraticElimination](../../../Math/LinearAlgebra/TwoSourceQuadraticElimination.lean)
   derives the cross term of a bilinear paired-field action, its stationary
   variation and the on-shell identity with arbitrary unequal sources.
3. [TypedVertex](../../../GUT/PatiSalam/Matching/TypedVertex.lean) constructs
   actual invariant RR and LR tensors, proves pure-field contraction identities,
   projects identical-fermion statistics, proves sector membership and nonzero.
   It uses the existing four-family dimension-seven framework; qque permission
   and species-copy surplus are not inputs.
4. [LightFields](../../../GUT/PatiSalam/Matching/LightFields.lean) embeds uR,dR,
   uL,dL and the anti-neutrino Weyl line into the actual field modules, evaluates
   the boson VEV and pulls back the alternating four-fermion coefficient.
   Cross probes vanish, so the two chiral coefficients cannot cancel as tensors.
5. [NeutralMass](../../../GUT/PatiSalam/Matching/NeutralMass.lean) proves
   the entire mu=0 kernel is x0 times (1,0,-d/M), M nonzero. Its finite-mu
   residual is (0,0,-mu*d/M), showing why that chart is not an exact finite-mu
   massless solution in general.
6. [ModelApplication](../../../GUT/PatiSalam/Matching/ModelApplication.lean)
   instantiates these parts, derives source-current matching and coefficient
   zero/nonzero conditions, and supplies an exact mass-compatible nonzero point.

## Formula And Hypotheses

For m, M, Lambda nonzero, write

\[
 k_X=-\frac{C_X v y\,\overline Y}{\Lambda m\overline M},\qquad d=Y\overline w,
 \qquad p=\overline{-d/M}.
\]

The two actual SM coefficients are k_L/2 times the LR seed and k_R times the
RR seed. The half accounts for the covariant QQ contraction. After VEV w and
light-field pullback the probes give -k_L*w/2 and -k_R*w/2, respectively.
The scalar-source identity gives k_X*w=C_X*v*y*p/(Lambda*m).
The source action uses quadratic coefficient -m and the oriented current -J;
its selected pure-field contractions are proved equal to these typed seeds.

`light_nonzero_iff` proves exactly

\[
 C_{\rm light}\ne0\ \Longleftrightarrow\
 w\ne0\land v\ne0\land y\ne0\land Y\ne0\land
 (C_L\ne0\lor C_R\ne0).
\]

All selected inverse conditions are explicit theorem parameters. Lean's total
division at zero does not legitimize eliminating a zero-mass field. In the
exact control all parameters are one, mu=0 and M=y*star(v); the kernel chart
is (1,0,-1), and both actual light probes give 1/2. This point is an exact
algebraic control, not a fitted hierarchy or canonical field normalization.
Zero UV coefficients, zero VEV/Yukawa/projection and independent chiral
controls are distinguished. A scalar same-output cancellation lemma does not
assert LR/RR tensor cancellation; nor does independence of tensors preclude
interference or cancellation in particular hadronic amplitudes.

## Remaining Inputs And Stop

| Phase | Checked part | Remaining boundary |
| --- | --- | --- |
| 1 | Typed SM supports, charge/conjugation dictionary, epsilon factors | Full PS branching/invariance and selected Higgs direction supplied; source-wide normalized dictionary unresolved |
| 2 | Signed scalar elimination; exterior assembly; VEV evaluation | No loops, momentum expansion or scalar-potential derivation |
| 3 | Exact mu=0 full mass kernel; barred projection; actual light nonzero iff | No canonical normalization or finite-mu spectral theorem |
| 4 | Conditional one-generation component instantiation and exact controls | Complete normalized agreement of Eqs.(10)–(24) unverified |

The stop is the frozen source-convention gate, not an assertion that the whole
paper matching certificate is complete. To continue that comparison, supply
or independently justify the mass/vertex sqrt(2) and kinetic normalization
conversion, then repeat the operator comparison in that dictionary. No new
model, rate calculation, SO(10) instance or foundational representation project
was started to bypass the gate. The exact nonzero statement in its recorded
chart remains valid; it does not depend on the unresolved prefactor conversion.

See the [reader-facing result](../../model-studies/pati-salam-protection/generated-coefficient.md),
[verification](verification.md) and [exact checks](../../../tools/ps-bnv-coefficient-bridge/README.md).

## Normalization Follow-Up

The [follow-up result](follow-up-result.md) derives unit normalization and
nonzero transport for the supplied exact mu=0 chart, and finite component
contraction identities. Full source-to-chart admission remains unverified.
