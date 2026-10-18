# Positive-Target Model on the E6 Candidate

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**The bounded actual-model package is complete.**

- [UnitaryRepresentation](../../../../../GUT/E6/Minuscule/UnitaryRepresentation.lean)
  defines the candidate's actual matrix action on `EuclideanSpace` of
  complex dimension 27. Unitarity follows from its SU(27) membership,
  joint continuity from matrix action, and `su5RestrictionEquiv` from the
  already constructed group-level intertwiner.
- [SU5Character](../../../../../GUT/E6/Minuscule/SU5Character.lean) takes traces of
  that actual equivalence. `su5_character` gives two trivial summands,
  one five, two dual fives and one ten; `su5_dual_index` cancels the
  vectorlike pair and singlets, retaining `10 + bar5` with positive orientation.
- [MinusculeBenchmark](../../../../../GUT/E6/SelectionRules/MinusculeBenchmark.lean)
  uses the existing actual SU(5) matter/physical-torus formulas to derive
  `restricted_dual_index` and `hasTarget`. The latter applies to every
  invariant symmetric mass on this restricted source, by the previously
  proved radical index conservation theorem. No target certificate is supplied.
- `model` and `continuousModel` are actual inhabitants with zero mass and
  trivial action of any Abelian residual group. `light_index_coefficient`
  proves coefficient `+1` at each of the 15 SM weights, and
  `exists_sm_zeroMode` gives actual nonzero radical vectors. `nonvacuous`
  applies the common supported selection-rule theorem to this model.

The zero-mass radical has dimension **27**, while the chosen one-generation
SM plus two neutral-singlet target has character **17** at the identity.
`radical_character_ne_target` proves that their full characters differ.
The exact equality is of **dual indices**, not full light spectra. The
extra vectorlike pair is not removed by a hidden mass assumption. Choosing
two singlets records the restriction; a dual index alone cannot determine
neutral-singlet multiplicity.

## 2. Inputs and conclusion

### Bounded Target

The user approved continuing after `checkpoint 01`. Construct an actual inhabitant
of the existing continuous standard-chain interface for
`compactIdentityComponent`, using its defining 27-dimensional action and
the proved SU(5) inclusion. Do not rename this carrier simply connected E6.

Acceptance criteria:

1. Actual continuous unitary action on the standard complex Hilbert 27,
   with the existing group-level restriction equivalence.
2. Derive its character and positive one-generation dual index from the
   actual `1 + 1 + 5 + bar5 + bar5 + 10` restriction. The vectorlike pair
   and neutral singlets cancel in the dual index, not in the full spectrum.
3. Derive the exact light dual target for every symmetric mass invariant
   under the restricted SU(5) torus and residual group.
   Construct a particular continuous model with zero mass and trivial
   residual action, then derive nonzero SM weight modes and the existing
   supported selection-rule conclusion. State that all 27 modes remain
   light in this particular example.
4. Persistent axiom and boundary audits, full regression, documentation
   and a thematic commit. Stop at this actual-model deliverable.

Planned modules: `Minuscule/UnitaryRepresentation`,
`Minuscule/SU5Character`, `ProtonStabilityNoGo/MinusculeBenchmark`, and its
audit. Reuse `SU5Inclusion`, SU(5) matter/torus characters and `StandardChain`.
No assumed branching/target certificate, new dependency, general Lie
integration, center or global-form classification is authorized. If the
positive orientation fails, record the discrepancy rather than changing
the target. Nonzero masses/couplings, an SM-only full spectrum, vacuum
dynamics and decay amplitudes are not deliverables of this package.

## 7. Sources and verification

### Verification and Stop

```sh
lake build GUT.E6.Audit.AuditMinusculeBenchmark
lake build
```

The [persistent audit](../../../../../GUT/E6/Audit/AuditMinusculeBenchmark.lean)
checks 33 declarations using only `propext`, `Classical.choice` and
`Quot.sound`, with 4424 targeted jobs. It instantiates discrete Z/3 and
continuous-circle residual groups, both acting trivially; checks physical
torus compatibility and nonzero modes; and rejects zero/negative target
orientation and full-character equality. These examples do not establish
a faithful or nontrivial residual action. Full regression results are in
[historical milestone record](../../../../topics/e6-global-topology/checkpoints/e6-sources.md).

The actual-model stop gate is reached. The candidate-group source and
positive-target existence inputs are now closed. Identification with the
intended global compact E6 remains unproved and deferred; no resumed
center/classification sequence, new dependency, axiom or external trusted
calculation is part of this package. No SM-only full spectrum, realistic
mass, vacuum, or decay-amplitude claim is added.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
