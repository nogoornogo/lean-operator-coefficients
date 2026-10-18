# Four-Weight QQue Criterion

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Statement

The qque-only endpoints need dual-index matching at **0, 3, 8, 14**, not at
all fifteen SM weights. The existing two actual ambient conjugations, actual
finite-dimensional source, strict commuting residual action and invariant
symmetric mass are retained. Only the Q target must be positive/nonzero.
The target at both Q slots is the same; Q/up/e compatibility is derived.

This is a weakening for the qque-only conclusions, not a replacement for the
stronger [two-signature result](../../inputs/Physics/TWO_CONJUGATIONS.md). It does not assert duql,
full-five-species support or minimality of the four weights.

## 2. Inputs and conclusion

### Checked Endpoints

[FourWeightQque](../../../../../Physics/StandardModel/Spectrum/FourWeightQque.lean):

- `of_partial_target`: the old fifteen-weight actual-source hypothesis implies
  the new one, with the same representation, mass and radical spectrum.
- `quark_profiles_compatible`: derives Q/up/e profile equality using target
  weights 0, 8, 14 and the two actual conjugators.
- `exists_supported_qque`: supplies a neutral qque assignment, operator-local
  slot support and nonzero actual radical eigenvectors at all four slots.
  The second Q witness uses the target equation at weight 3.
- `slotwise_selection_rule_obstruction`: refutes the same slotwise universal
  prohibition as the previous Q-only endpoint. It does not refute the legacy
  full-support predicate when spectator species are absent.

[FourWeightLightQque](../../../../../Physics/StandardModel/Operators/FourWeightLightQque.lean):

- `of_matches`: restricts the previous H-character target to the four weights.
- `characters_compatible`: derives Q/up/e character equalities.
- `common_quotient`: extracts one common nonzero irreducible split quotient
  from the actual light spaces at the four slots, using finite-group
  semisimplicity and the positive actual Q target.
- `exists_qque_coefficient`: constructs a nonzero H-intertwiner
  `(Q_0 tensor Q_3) tensor (u_8* tensor e_14*) -> C`.
- `not_forbidsBothInternalCoefficients`: the qque coefficient alone rules out
  vanishing of both coefficient spaces. No duql coefficient is claimed here.

The old qque slot-neutrality identity is unchanged. The starred spaces are
contragredients of the actual left-chiral sectors, not assumed light projections.

## 4. Proof structure

### Target And Support

[QqueLocalTarget](../../../../../Physics/StandardModel/Spectrum/QqueLocalTarget.lean)
defines `Monitored i` as `i = 0 or 3 or 8 or 14`. `Matches p P` requires

```text
m(w_i,q) - m(-w_i,-q) = P_species(i)(q)
```

only for monitored i and every residual charge. The opposite-weight term is
not removed. No matching equation is imposed at the other eleven weights;
actual representation and conjugation identities still hold globally.
The existing five-species profile container is reused, but its down/lepton
entries impose no conditions: `matches_iff_of_profiles_eq` proves this.

The Abelian source requires unitarity of T x H. H is arbitrary Abelian,
including finite groups, with no topology required. The finite non-Abelian
source requires only torus unitarity; H is finite. Its target equation is
the analogous H-character-valued difference on the actual weight spaces.
Unused down/lepton entries of that existing target container likewise impose
no matching or nonzero-target hypothesis. The finite-dimensional target
family convention is retained.

## 6. Scope and limitations

### Controls And Boundaries

Persistent audits cover every new theorem and permit only `propext`,
`Classical.choice`, `Quot.sound` transitively. Controls check:

- Fifteen-weight targets imply the four-weight predicates in both routes.
- A profile-level example has positive Q and satisfies the four-weight target
  but fails the fifteen-weight target. This is not a new ambient source model.
- A zero spectrum cannot supply the chosen positive Q target.
- The earlier lepton-triality target, even restricted to these four weights,
  cannot come from an actual source with the two conjugators. Q/electron
  mismatch suffices; no down/lepton matching is used by this control.
- Changing unused target entries does not change either predicate.

No claim is made here about full SM-gauge invariance on arbitrary radicals,
Lorentz/Grassmann nonvanishing, generated
couplings, amplitudes, lifetimes, or additional physical embeddings. The E6
literature boundary is unchanged. The [assumption ledger](../../../ASSUMPTIONS.md)
distinguishes this qque-only weakening from the retained pair theorem.

Plan and verification: [topic record](../../../../topics/four-weight-qque/README.md).

The [compact-H API audit](../../../../topics/compact-residual-api/README.md) checked the
ingredients for removing finite H. Its successor, the separate
[compact continuous qque theorem](COMPACT_LIGHT_QQUE.md), connects those
ingredients to the actual light spaces under explicit residual continuity.
The finite endpoint above remains unchanged and requires no topology on H.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
