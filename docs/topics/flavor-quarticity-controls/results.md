# Results and Adapter Assessment

## DGT Restricted SM/Higgs and Dipole Comparison

[DgtFlavorRestriction](../../../Physics/StandardModel/Operators/DgtFlavorRestriction.lean)
implements the m=1,n=3 instance of
[2202.05275v2](https://arxiv.org/pdf/2202.05275v2), Table I, Secs. II–III.
The existing signed ten-species dictionary has family charge
X(u,i)=baryon(u)-9 lepton(u) delta_(i,mu), where baryon=3B_usual.
Printed physical quarks have charge one, electron/tau zero, muon minus nine.
Opposite charges are proved. Both Higgs species have trivial residual action.

`embedding` injects Z9 into Circle using the standard cyclic character.
`phase_restriction`, `charge_restriction`, `flavor_restriction` and
`actual_field_restriction` prove the restriction on the actual gauge/Weyl
fields, not merely integer residue agreement. `scalar_restriction` handles the
neutral Higgs copy action. `condensate_fixed` checks that charge-nine scalar
insertions are neutral under the constructed subgroup; no dynamical VEV is
assumed or derived. The zero-charge singlet is automatically neutral.

On the residual SM/Higgs domain `all_bnv_forbidden` and
`residual_bnv_forbidden` prove absolute B1/B2 prohibition at every
fermion/scalar degree through ComposableBLSupport. Three complex copies per
fermion and one scalar copy per Higgs species are explicit.

`electronUV_eq` and `electron_restriction` identify the charged right-lepton
flavor action with the action used by the dipole adapter.

On the separate actual dipole domain the lepton representations restrict to
a trivial Z9 action. The two selectors prescribe muon-to-electron and
muon-to-tau gauge-basis flavor coordinates. `uv_dipoles_forbidden` proves
both selected B/W channel pairs vanish under the Circle action. `irWitness`
and `irWitness_selected` construct a coefficient for each pair with selected
value (1,0) under Z9. This is actual invariant-coefficient existence, not only
charge neutrality. No UV-generated interaction or mass-basis LFV is inferred.

`restrictMap` restricts the same underlying flavor intertwiner along the
proved embedding. `bridge_not_restricted` and `restriction_not_surjective`
prove that the residual bridge witnessing a selected coefficient does not
lift to a UV-invariant bridge. This supplies an explicit obstruction to
surjectivity on that Hom factor, the type of condition used by the
coefficient-space symmetry-extension criterion. No global identification of
the mixed SM support and the dedicated dipole domain is claimed.

This agrees with the paper's distinction: exact residual baryon protection
persists, but residual invariance does not enforce its UV muon selection.
The paper's higher-dimensional dressed interactions, leptoquark/nuR alphabet,
complete UV model, anomaly cancellation, matching and rates are not certified.

## Quarticity: Bare and Eta-Dressed Coefficients

[QuarticityAdapters](../../../Physics/StandardModel/Operators/QuarticityAdapters.lean)
uses the full SM-cover gauge group, the existing SL(2,C) right-Weyl action,
and residual Z4 times Z2. Its selected right-handed-neutrino carrier is a
single Weyl spinor, with trivial SM gauge action and residual charges (1,1).
The eta singlet has charges (2,0). These match Table I and Eqs. (1),(11) of
[1606.04543v1](https://arxiv.org/pdf/1606.04543v1).

`neutrino_action`, `eta_action` and both gauge-neutrality lemmas verify these
adapters. `eta_phase_square` and `eta_phase_real` prove eta's residual phases
are real signs. Its complex coefficient carrier is the complexification of
the selected real singlet; real-field dynamics are not part of this result.

`Bare` is the invariant functional space on the actual exterior square of
the right-handed neutrino. `bare_forbidden` proves every such functional is
zero, using a Z4 element whose pair phase is nontrivial. Exterior statistics
are retained; the spinor contraction is not replaced by a symmetric spinor
bilinear.

`Dressed` is the invariant functional space on that exterior square tensor
the eta carrier. `epsilonExterior` descends the two-dimensional determinant
through the exterior-power universal map. `epsilon_neutrino` checks its actual
right-Weyl action. `compensated` cancels both residual phases including Z2.
`dressed` is therefore an actual invariant coefficient, with
`dressed_evaluation=1` on two independent basis spinors and eta=1.
`dressed_nonzero` and `exists_dressed` certify nonzero existence.

`sm_lTwo_forbidden` separately proves all-degree absolute L2 prohibition on
the original SM/Higgs-only alphabet through ComposableBLSupport. This does
not prohibit the extended neutrino/eta operator. Fermionic lepton number two
and total quarticity two cease to describe the same target when eta is added.
No embedding of the complete extended alphabet into the original SM/Higgs
input is asserted.

## Burden and Boundaries

Both adapter routes succeeded with existing representation, determinant,
exterior, tensor and cyclic-character APIs. New source consists of two bounded
application modules and one audit; no new foundations or dependencies were
needed. The selected one-neutrino-copy certificate does not classify all
flavors or all operators of either paper. Neutrino masses, vacuum dynamics,
dark-matter stability as a physical particle statement, cosmology and rates
remain outside the endpoint. See [verification](verification.md).
