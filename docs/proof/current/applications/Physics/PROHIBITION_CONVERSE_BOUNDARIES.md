# Bounded Converse Criteria and Controls

## Inputs and exact outcomes

The completed [topic](../../../../topics/prohibition-converse-boundaries/README.md)
uses existing actual coefficient, representation and mass interfaces. Its
statements remain separate from generated interactions, rates, vacua and UV
models. No external physical premise or dependency change is introduced.

For positive cyclic order and finite diagonal flavor modules, arbitrary mu
and ell select a nonzero actual B/W dipole coefficient iff some matching-charge
coordinate pair has nonzero mu(i) and ell(e_j). Charge overlap alone is not
sufficient for arbitrary selectors. This exact support criterion reuses the
actual intertwiner-evaluation equivalence and explicit equivariant matrix units.
See [LFV result](../../../../topics/prohibition-converse-boundaries/lfv-results.md).

For equal source/target residual copy representations s in Q/uc/ec and an
actual invariant zero mass, proved commuting squares and zero-kernel splits
leave nonzero participating light exterior qque coefficients. Every tested
r has equal Hom dimensions and no surplus. This refutes the numerical converse
within the original arbitrary-mass scope without changing its sufficient
surplus theorem. See [counterexample](../../../../topics/prohibition-converse-boundaries/surplus-results.md).

In the actual full-SM restriction of the fixed 10/bar5/40/50 dual-copy family,
net copies (N,N,0,0) are equivalent to existence of some symmetric invariant
mass whose radical is equivariantly N SM generations. Copy-sum equivalences,
reassociation, evaluation-pair mass and equivariant pullback construct the
reverse. This does not assert every consistent mass works. The explicit
zero-mass control retains a nontrivial vectorlike sector. No SU(5)-invariant
UV action or VEV certificate follows. See [mass result](../../../../topics/prohibition-converse-boundaries/copy-mass-results.md).

For stable selected mixed contents with actual scalar cyclic flavor actions,
prohibition at all degrees iff every selected nontrivial local/statistics
carrier has nonzero total cyclic charge. Zero carriers require no detection.
The same criterion is transported to the signed SM/Higgs coefficient facade.
Lorentz central parity forbids every odd fermion degree; the lepton-parity
input gives a neutral raw triple-Q B1 control despite all-degree prohibition.
Thus the unguarded raw filter is not necessary. The guarded criterion is not
a computed full classification of SM support or q/l parameters.
See [all-degree result and stop boundary](../../../../topics/prohibition-converse-boundaries/all-degree-results.md).

## Sources and proof verification

- [CyclicSelectorDipoleSelection](../../../../../Physics/StandardModel/Operators/Dipole/CyclicSelectorDipoleSelection.lean).
- [BalancedSpeciesSurplusControl](../../../../../Physics/FieldTheory/Mass/Surplus/BalancedSpeciesSurplusControl.lean).
- [CopySumEquivalence](../../../../../Math/RepresentationTheory/Multiplicity/CopySumEquivalence.lean).
- [ActualFullFamilyMassExistence](../../../../../GUT/SU5/SelectionRules/ActualFullFamilyMassExistence.lean).
- [AdmittedCyclicProhibition](../../../../../Math/RepresentationTheory/Protection/AdmittedCyclicProhibition.lean).
- [AdmittedCyclicSMProhibition](../../../../../Physics/StandardModel/Operators/Selection/AdmittedCyclicSMProhibition.lean).

The [Math audit](../../../../../Math/RepresentationTheory/Protection/Audit/AuditProhibitionConverseBoundaries.lean),
[Physics audit](../../../../../Physics/StandardModel/Operators/Selection/Audit/AuditProhibitionConverseBoundaries.lean)
and [GUT audit](../../../../../GUT/SU5/Audit/AuditFullFamilyMassExistence.lean)
check all 37 new declarations transitively, allowing only propext,
Classical.choice and Quot.sound. Builds, checks and intermediate corrections
are recorded in [verification](../../../../topics/prohibition-converse-boundaries/verification.md).
