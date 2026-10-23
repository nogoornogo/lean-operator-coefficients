# Boundary-Selected SU(6) Baryon Protection

The algebraic boundary construction of [Angelescu et al.,
2104.07366v2](https://arxiv.org/html/2104.07366v2), (4)–(10) and Appendix C,
now has an actual SU(6) exterior-representation connection in Lean. The
constructed unmixed boundary amplitudes carry the standard SM action and a
residual baryon phase. That phase prohibits absolute baryon-number change
one (B1) on the associated SM/Higgs coefficient input at every nonderivative
degree. A separate theorem applies the same obstruction to selected sources
with full stable derivative/EOM/IBP relations.

The formal result ends at algebraic amplitudes and internal contractions.
Analytic bulk mode equations, spectrum after nonzero brane mixing, scalar
potential minimization and quantum protection are separate inputs. The paper
itself identifies a baryon anomaly. The construction therefore supplies an
algebraic protecting input, without certifying a complete quantum or realistic
five-dimensional model.

## Boundary Input And Exact Light Components

Repository coordinates are color, weak, singlet (3,2,1); the source puts weak
before color. The SM cover acts by diag(z^(-2) A, z^3 B, 1), with integer
hypercharges measured in units of 6Y. A plus sign retains a boundary amplitude.
Both signs are complemented for right chirality.

| Bulk carrier | Left UV / IR retained components | Exact unmixed selection |
| --- | --- | --- |
| 20 = exterior cube of 6 | UV none; IR the complement of color wedge weak wedge weak | Left zero; right u, with 6Y=4 |
| 15 = exterior square of 6 | UV uc,Q,ec; IR Q,ec,color–singlet,weak–singlet | Left Q and ec; right zero |
| 6 | UV and IR singlet | Left neutral singlet; right d and conjugate L |
| 1 | UV all; IR none | Neither chirality |

[ChiralSelection](../../../GUT/SU6/Boundary/ChiralSelection.lean) proves the
selected spaces exactly. `actual_left15_exact` transports through the existing
SM-equivariant exterior-square equivalence. `right20Equiv` uses an explicit
embedding j and contraction p with pj=id. `right6Equiv` identifies the two
right blocks; the existing SU(2) epsilon equivalence identifies their dual
weak block with the usual left lepton.

The [cube construction](../../../GUT/SU6/Boundary/ExteriorCube.lean) derives
j and p from exterior multiplication, its coproduct and the weak volume form.
Both intertwine the actual SM action. It does not assume a 20-component
branching table. The [shared projector theorem](../../../Math/LinearAlgebra/Boundary/Projectors.lean)
identifies the common retained space with the image of the product of two
commuting projectors and proves preservation under commuting actions.
These selected amplitudes are not identified with a finite symmetric-mass
radical.

## Genuine Residual Action

Use an integral double cover of the source's baryon circle. For t in Circle,
construct the SU(6) homomorphism

$$
s(t)=\mathrm{diag}(t I_3,t^{-1}I_2,t^{-1}),\qquad
D(t)=t\,s(t)=\mathrm{diag}(t^2 I_3,I_2,1).
$$

[exterior_factor](../../../GUT/SU6/Boundary/BaryonAction.lean) proves, for every
exterior degree n, that the induced action is t^n times the actual exterior
SU(6) action of s(t). This derives the bulk central phases 3,2,1,0 from one
functorial identity. The resulting integral charge is 6B: two per color slot,
zero per weak or singlet slot.

The action preserves the boundary projectors, commutes with the retained SM
action, fixes the singlet scalar VEV and fixes the actual weak–singlet Higgs
endomorphism under conjugation. The resulting all-left charges on
(Q,uc,dc,L,ec) are (2,-2,-2,0,0). Right-handed conjugates have the inverse
phase, as proved by `dual_phase`.

Restricting t to fourth roots gives a genuine C4 action with quark character
2 and neutral leptons/Higgs. The action on those fields has a C2 image; no
faithfulness on the light space or anomaly-free discrete symmetry is claimed.

## Boundary Interactions

[Interactions](../../../GUT/SU6/Boundary/Interactions.lean) checks internal
contractions compatible with the source's UV and IR mass mixings:

| Source channel | Constructed contraction | Residual invariance |
| --- | --- | --- |
| UV 20/15 | Dual twenty evaluated on scalar wedge fifteen | `uv_20_15_invariant` |
| IR 15/20 | Dual fifteen evaluated on conjugate-scalar contraction of twenty | `ir_15_20_invariant` |
| IR 6/15, color and weak blocks | Dual six evaluated on conjugate-scalar contraction of fifteen | `ir_6_15_invariant` |
| IR 1/6 | Dual singlet evaluated on the six's singlet coordinate | `ir_1_6_invariant` |

The source calls chi left-handed and barred psi right-handed. Its unbarred
psi is consequently a dual field. The UV central balance is 1-3+2=0;
treating psi as a direct field gives charge 6, which is detected by C4.
`wrong_conjugation_not_invariant` checks this convention error explicitly.
The scalar/conjugate-scalar orientation of the contractions is derived here;
Eq. (10) prints the mass terms after symmetry breaking. The fundamental
scalar slot realizes the fixed internal VEV; full boundary scalar gauge
representations and scalar Lagrangians are not admitted here.

`strip_join_pure` and `stripSquare_vev` prove retraction identities on the
relevant scalar-free vectors, so these invariance statements do not merely
certify zero maps. Coefficient values, flavor matrices, Lorentz contractions,
kinetic normalization and the full printed brane action are not matched.

## Coefficient And Relation Interfaces

[Protection](../../../GUT/SU6/Boundary/Protection.lean) derives the actual light
gauge/residual dictionary. `bounded_light_forbidden` connects it to the existing
three-generation coefficient interface; `neutral_control` restores an actual
nonzero bounded coefficient when the residual action is omitted.

[BaryonParitySelection](../../../Physics/StandardModel/Operators/Selection/BaryonParitySelection.lean)
proves all-degree vanishing for arbitrary complex generation/multiplicity
spaces and any number of Higgs/conjugate-Higgs insertions. The ten signed SM
species have charge twice their integer 3B charge. At B1, total charge is
+6 or -6, both nonneutral modulo four. The proof uses the actual exterior /
symmetric tensor coefficients and their scalar-action constraint.
The neutral sterile field and other exotic alphabets are not added to this
SM/Higgs coefficient theorem.

`derivative_selected_forbidden` takes the existing `DerivativeInterface.Input`,
a stable selected subspace and its baryon-charge action. Relations are pulled
back from the full source, including nonlinear EOM that mix field degrees.
It proves vanishing in the selected quotient without assuming that its
coefficients extend globally. Full-relation stability and the selected charge
law are explicit hypotheses; no paper-wide interacting EOM module is supplied.

## Admission Boundary

To turn this amplitude construction into a statement about the paper's mixed
five-dimensional light modes, supply the analytic mode-identification map,
its inverse/exhaustiveness and gauge/residual equivariance. Nonzero brane
mixing changes the boundary problem; the unmixed projectors do not prove that
mixed spectrum. `transport_forbidden` records the coefficient-equivalence
transport once such an identification is independently available.

No mass-radical premise from the [standard-class obstruction](feasibility.md)
is substituted for this mode certificate. The two results concern different
light-state mechanisms and are consistent. The remaining analytic, quantum,
matching and numerical questions do not block this algebraic endpoint.

See the [source correspondence and checks](../../topics/su6-protection-feasibility/boundary-verification.md)
and the [topic contract](../../topics/su6-protection-feasibility/boundary-plan.md).
