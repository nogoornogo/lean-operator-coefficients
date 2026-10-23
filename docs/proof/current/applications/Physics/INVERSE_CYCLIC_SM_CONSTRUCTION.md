# Inverse Cyclic SM Construction

## Statements and hypotheses

The finite charge filter fixes generation-universal charges, three SM
fermion generations, a neutral Higgs doublet and its conjugate, and cyclic
orders 2 through 12. Neutrality of the three charged-fermion Yukawa signatures
reduces five all-left charges to (q,-q,-q,l,-l). The necessary bounded-BNV
constraint is 3q+l != 0. Kernel-checked finite counts leave 572 of 649 labeled
pairs. These are necessary arithmetic candidates, not protecting models.

The first pair, (k,q,l)=(2,0,1), has a constructed SM x Z2 action. Each of its
five species is gauge-equivariantly three standard copies. The original
invariant symmetric mass is the orthogonal sum of zero SM mass and a charged
singlet/dual evaluation pair. Its radical is explicitly equivariantly the SM
light space. The result uses no supplied radical or nonzero-operator premise.

`construction_certificate` bundles that actual radical equivalence, nonzero
original mass, nonzero Yukawa exterior coefficients in all three charged-
fermion channels, the filter witness, and all-degree B1 prohibition on the
same named field/action input. The phase is before electroweak breaking.

## Proof sources and structure

- [Charge filter](../../../../../Physics/StandardModel/Operators/Selection/InverseCyclicSMCharges.lean):
  Yukawa parametrization, signed-charge dictionary, actual one-generation
  bounded iff and three-generation DUQL-based necessity, finite cardinalities.
- [All-degree selection](../../../../../Physics/StandardModel/Operators/Selection/InverseLeptonParitySelection.lean):
  scalar action on actual fields, even-fermion Lorentz constraint, parity of
  summed baryon/lepton labels, and selected all-degree vanishing.
- [Spectator radical](../../../../../Physics/FieldTheory/Mass/Surplus/ConstructedSpectatorRadical.lean):
  generic constructed invariant mass and exact radical equivalence.
- [Actual realization](../../../../../Physics/StandardModel/Spectrum/Representations/InverseCyclicSMRealization.lean):
  actual chiral carriers, three-copy equivalences, coefficient group/tensor
  regrouping, flavor duals, spectator mass and neutral Higgs action.
- [Gauge Yukawa contractions](../../../../../Physics/StandardModel/Gauge/Tensors/SMYukawaContractions.lean):
  hypercharge-preserving contractions and explicit nonzero basis values.
- [Two-species descent](../../../../../Physics/FieldTheory/Yukawa/Mass/TwoSpeciesExteriorYukawa.lean)
  and [spinor contraction](../../../../../Physics/FieldTheory/Yukawa/Mass/SpinorYukawaContraction.lean):
  generic distinct-species exterior descent after a genuine Weyl contraction.
- [Actual Yukawa consumer](../../../../../Physics/StandardModel/Operators/Selection/InverseCyclicSMYukawa.lean):
  residual/flavor contraction, physical exterior nonzero statements and bundle.

A nonzero coefficient forces even total fermion degree n and even total L.
On the ten signed SM species, 3B+L=n modulo 2, so absolute 3B=3 cannot occur.
The all-degree endpoint is not inferred from the bounded four-family filter.
Its selected-domain vanishing is transported to residual-Hom coordinates by
the existing coefficient-space decomposition.

## Applicability and boundaries

The finite filter is complete only for its stated arithmetic predicate. No
symmetry-equivalence reduction or physical-model enumeration is performed.
The successful action is familiar lepton parity, not a new physical model.
Its imposed algebraic symmetry is not certified anomaly-free or quantum exact.
The spectator block demonstrates a mass realization, not a dynamical symmetry
or VEV mechanism. No simple-group lift is supplied. Yukawa nonzero witnesses
do not certify realistic mass rank, mixing or generated couplings.

Only the specified derivative-free SM fermion/Higgs alphabet is covered.
Gauge-strength fields, derivatives, EOM/IBP, extra light particles and quantum
or observable effects require separate statements. The result is an actual
algebraic construction satisfying the declared coefficient constraints;
it must not be described as physical proton stability.

## Verification and provenance

The [persistent audit](../../../../../Physics/StandardModel/Spectrum/Representations/Audit/AuditInverseCyclicSMConstruction.lean)
checks the result and reusable helpers transitively with only propext,
Classical.choice and Quot.sound. Verification commands and outcomes belong to
[the topic record](../../../../topics/inverse-cyclic-sm-construction/verification.md).
Existing local field, character, Lorentz and mass assets supply the inputs;
no new external literature premise, dependency pin or audit exception is used.

## Completed bounded converse

`InverseCyclicSMCharges.three_generation_forbidden_iff` closes the same
three-generation dimension-six DeltaL=1 criterion: prohibition iff 3q+l != 0
modulo k, for every positive k. All four neutral-coordinate sets are empty
when the common charge is nonzero, including QQUE symmetric pairs and all
QQQL Young branches. Neutrality supplies an actual DUQL coordinate.
Candidate membership and non-membership are equivalent to bounded prohibition
and allowance respectively. Thus the 572 survivors classify this bounded
predicate exactly; they still do not classify all-degree protection or UV
realization. See [the converse result](../../../../topics/inverse-cyclic-sm-construction/bounded-converse-results.md).

## Selected coefficients and charge equivalence

The [follow-up result](../../../../topics/inverse-cyclic-sm-construction/three-followups-results.md)
proves selected dipole allowance iff the selected charges agree in finite
diagonal cyclic modules, using normalized basis/projection selectors.
A matrix unit supplies the converse without a semisimplicity premise.
One-copy B2 and neutral-Higgs LLHH domains satisfy prohibition iff 6q != 0
and 2l != 0 respectively; no three-generation extension of these domains
is asserted.

Unit scaling of both charges at a fixed order is an equivalence relation
and an actual cyclic group generator relabeling. It preserves the three
charge tests and effective phase-image size. Kernel enumeration gives 151
unit orbits among 572 tuples. The phase-image cardinal counts distinguishable
actual universal field phase pairs, not full model equivalence.
The [follow-up audit](../../../../../Physics/StandardModel/Operators/Selection/Audit/AuditInverseCyclicFollowups.lean)
checks all new declarations transitively under the same standard axiom policy.
