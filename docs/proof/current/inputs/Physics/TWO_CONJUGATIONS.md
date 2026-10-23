# Two-Conjugation Selection Rules

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Result

For qque alone, the later [four-weight target refinement](../../applications/Physics/FOUR_WEIGHT_QQUE.md)
removes eleven matching equations. The pair theorem documented here retains
the fifteen-weight target.

Two actual ambient elements implementing `(3 1)` and `(0 4)` on the fixed
SM weight torus suffice. There is no input element for `(0 3)`.
The old three-element certificates convert via `ThreeConjugations.toTwo`;
the old theorems remain unchanged.

The minimum requested endpoint was a supported neutral qque signature. Under
the retained target at all fifteen SM weights, the checked result is stronger:
**both qque and duql survive**, with the same positive Q/down inputs as before.

## 2. Inputs and conclusion

### Abelian Endpoints

[TwoConjugationQque](../../../../../Physics/StandardModel/Spectrum/Representations/TwoConjugationQque.lean)
retains an actual finite-dimensional G x H representation, arbitrary Abelian
H, restricted unitarity, an invariant symmetric mass, the local dual SM target
and the actual radical spectrum. H need not be finite or torsion-free.

- `exists_supported_qque` needs only positive Q total. It supplies a neutral
  qque charge assignment, support for its actual fields, and nonzero radical
  eigenvectors at the four slots 0, 3, 8, 14.
- `slotwise_selection_rule_obstruction` rules out forbidding every physically
  admissible signature whose appearing field slots are supported.
- `exists_actual_signature_pair`, with positive Q and down totals, supplies
  the original full-support qque/duql pair and all fifteen actual eigenvectors.
- `selection_rule_obstruction` has precisely the old
  `ForbidsEverySupportedPhysicalDeltaBOneOperator` conclusion, now from two moves.

The separate positive totals need not agree. Down/lepton equality and lepton
positivity for the pair are derived, not new assumptions.

### Finite Non-Abelian Endpoint

[TwoConjugationLightQque](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/TwoConjugationLightQque.lean)
accepts finite H without commutativity, positive actual representation-valued
local targets, and the same actual torus/mass/conjugation interface as the
[previous source bridge](../../../../topics/nonabelian-light-source/results.md).

It derives Q/up/e character equality and common split light quotients, hence
the nonzero ordered qque residual internal coefficient with nonzero Q target
only. The extra weight relation also derives down/lepton character equality;
with nonzero down target, `both_coefficients_exist` supplies both previous
ordered internal coefficients at the same torus-neutral slots.

## 4. Proof structure

### Why The Pair Survives

The original proof used representative weights 0, 8, 14 for Q/up/e and
9, 13 for down/lepton. The first two conjugations identify the three former
profiles. The third was used to connect down weight 9 with lepton weight 13.
But the existing Q/up permutation `(3 1)` also connects down weight **10**
with lepton weight **13**:

```text
permuteReducedWeight (swap 3 1) (smReducedWeight 10) = smReducedWeight 13.
```

This is a kernel-checked coordinate identity, not a sampled calculation.
The target assigns the same species profile/representation to each weight of
that SM multiplet. Thus the extra relation derives down/lepton compatibility
without constructing a third ambient element. No multiplication relations
between the two representatives are required.

### Support Is Not Discarded

The legacy `ChargesSupported` requires all five species, even for qque which
contains no down or lepton slot. [SlotSupport](../../../../../Physics/StandardModel/Operators/Selection/SlotSupport.lean)
adds a separate operator-local predicate; it does not modify the old one.
Full support implies slot support. The qque predicate checks Q/up/e supports,
while the source theorem additionally produces the actual four zero modes.

The control `legacy_prohibition_of_no_lepton` shows why this distinction
matters: the old universal prohibition is vacuous when there is no supported
lepton. Consequently the Q-only theorem does not assert its negation. The
full-support pair retains positive down total, deriving positive lepton total
from the checked second use of `(3 1)`. An independent spectator-occupancy
adapter is also retained, but no extra lepton assumption is needed by the
main pair theorem.

## 6. Scope and limitations

### Controls And Boundaries

The [persistent audit](../../../../../Physics/StandardModel/Spectrum/Representations/Audit/AuditTwoConjugationQque.lean)
also proves `triality_no_two`: an actual unitary mass source matching the
retained triality light target cannot possess these two conjugations. The
previous counterexample is therefore not accidentally admitted.

This is a reduction of sufficient inputs, not a proof that two is minimal,
that every embedding admits them, or that additional physical models have
been exhibited. The all-fifteen species-uniform local target is still required.
The Abelian endpoint concerns supported signatures; the finite non-Abelian
endpoint concerns residual internal coefficients. Neither implies a full
SM-gauge/Lorentz/Grassmann operator on arbitrary radicals, nonzero interaction
or decay amplitude, or a lifetime bound. The E6 literature boundary is unchanged.

Plan, commits and verification: [topic record](../../../../topics/two-conjugation-qque/README.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
