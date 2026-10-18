# SU(5) ordinary-Abelian matter source

## 1. Result And Status

Declaration map for the established interfaces below. Ordinary Abelian actions
on retained SU(5) matter give actual supported fields and nonzero invariant
ordered internal tensors.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

SU5-4: `LEAN-CHECKED`, stage 01.

## 2. Inputs And Conclusion

The source has n copies of each continuous unitary 10 and bar5, with n > 0; the
residual group is Abelian but need not be finite or topological.

### Scope

The source is the actual Hilbert sum of `n` copies each of the continuous
unitary `10` and `bar5` constructed in [SU5-3](su5-matter.md). An ordinary
action is any homomorphism from `H` into the full unitary centralizer of
that SU(5) action. The classification does not assume its multiplicity form
and does not impose determinant one on the residual symmetry.

For any commutative group `H` and `n > 0`, the source supplies five injective
SM field maps with residual characters. Within the selected `10` sector,
Q, u^c, e^c share a character; within the selected `bar5` sector, d^c, L
share a character. These equalities are derived from the actual action and
branching, not supplied as source hypotheses. Both supported operator
signatures have zero residual charge. Nonzero invariant ordered internal
`qque` and `duql` tensors are constructed on the actual field ranges and
their contragredients.

No finiteness or topology is required of `H`. In particular finite Abelian
groups, character multiplicities, and generation mixing are allowed. The
result selects suitable sectors; it does not say every generation choice
gives an invariant tensor. A nonzero eigenvector defines a complete copy of
the constituent, not just a nonzero formal-character coefficient.

This retained matter class has no heavy-field/mass-removal prescription.
There is no assertion about arbitrary SU(5) Lagrangians, a dynamically
selected vacuum, a Wilson coefficient, or a decay amplitude. The tensors
are ordered internal tensors, not a proved nonzero Grassmann/Lorentz
operator. The subsequent [SU5-5 assembly](../../../applications/GUT/interfaces/su5-final.md) packages the scoped
endpoint and one-generation constructor without enlarging these assumptions.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

The unitary centralizer determines multiplicity actions; full character sectors
and branching injections supply the actual supported tensor ranges.

### Proof Chain

1. [ExplicitMultiplicity](../../../../../../Math/RepresentationTheory/Multiplicity/ExplicitMultiplicity.lean)
   applies Schur's lemma to each copy-to-copy entry of a commuting operator
   on named, pairwise inequivalent irreducibles. Off-diagonal entries vanish
   and diagonal entries are scalars. The existing Hilbert amplification
   theorem supplies adjoints/unitarity; its closed embedding supplies the
   topology. `unitaryEquiv` is a two-sided continuous group equivalence
   `product U(m_i) = unitary centralizer`. No arbitrary algebra isomorphism
   is asserted to preserve the adjoint.
2. [MatterSource](../../../../../../GUT/SU5/SelectionRules/MatterSource.lean)
   specializes the proved irreducibility and inequivalence of actual
   `10`/`bar5`. `centralizerEquiv` identifies its centralizer with
   `U(n) x U(n)`. `multiplicityAction`, `sectorAction`, and
   `action_eq_multiplicity` derive the two matrix actions from an arbitrary
   `OrdinaryAction`. `ofFactors` supplies the inverse constructor.
   `gauge_unitary` and `gauge_jointlyContinuous` check unitarity and joint
   continuity of the finite-generation gauge action itself.
3. [UnitaryCharacterSectors](../../../../../../Math/RepresentationTheory/Characters/UnitaryCharacterSectors.lean)
   uses pinned TauCeti's simultaneous-eigenvector theorem for commuting
   operators. Unitarity puts the eigencharacter in `Circle`. A nonzero
   orthogonal-complement argument proves that the **full** character
   subspaces span the whole space; distinct character subspaces are
   orthogonal. No family-universal character or chosen eigenbasis is an
   input. [ResidualSectors](../../../../../../GUT/SU5/SelectionRules/ResidualSectors.lean)
   applies this to both generation spaces and constructs injective copies
   that intertwine the gauge action and carry the derived residual character.
4. [SupportedFields](../../../../../../GUT/SU5/SelectionRules/SupportedFields.lean)
   composes these copies with the actual full-group branching maps.
   `Realization` records an injective map into the matter space and proves
   its gauge/residual action laws; `Support` contains all five such maps.
   `exists_supported_compatible` constructs it from any positive-generation
   source. `supported_neutral_signatures` applies the shared charge
   cancellation and the checked dimension-six, Delta-B/Delta-L = 1
   signature counts. The right-handed sign convention is explicit.
5. [SupportedTensors](../../../../../../GUT/SU5/SelectionRules/SupportedTensors.lean)
   defines field spaces as the ranges of those actual injections.
   `fieldRepresentation_val` proves their action is the restriction of
   `R(h) gauge(SM(g))`, not merely an unrelated representation on an
   isomorphic space. `chargedDualEquiv` inverts the residual character;
   `rightSplit` uses the proved bidual equivalence to realize right-handed
   fields. Equivariant split projections pull back the shared tensors and
   preserve nonvanishing. `exists_supported_tensors` quantifies over all
   ordinary Abelian actions and constructs both nonzero invariant forms.

The source only uses the fixed standard embedding. Its tensor action is
stated on the SM covering group times `H`; SU5-5 additionally descends the
supported field/tensor actions to the exact SM quotient. No new kernel or
vacuum classification is being asserted here.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

## 6. Scope And Limitations

No heavy-field removal, arbitrary Lagrangian, Grassmann/Lorentz nonvanishing or
decay-amplitude conclusion is added.

## 7. Sources And Verification

The [scope dossier](../../../applications/GUT/SU5_SELECTION_RULE.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Persistent Audit

[AuditMatterSource](../../../../../../GUT/SU5/Audit/AuditMatterSource.lean) rejects any
transitive `GUT.SU6` import and checks:

- The trivial action has a full trivial character sector.
- An actual action of the two-element group `Int.units` swaps the two
  generations of `10` and fixes both `bar5` copies. Its generation action
  is not scalar. Its vectors `(1,1)` and `(1,-1)` carry the even/odd
  characters; the trivial `bar5` character has a repeated sector.
- This finite mixing source has nonzero invariant tensors on actual ranges.
- Zero generations admit no nonzero `Mode`; positivity is essential to
  field support, not an unchecked convention.
- In one actual `10`, no SU(5)-commuting action can fix a nonzero u^c
  vector while negating a nonzero e^c vector. The negative control uses
  actual branching injections. It is an incompatible IR assignment, not a
  counterexample source and not a prohibition on family-dependent actions.

```sh
lake build GUT.SU5.Audit.AuditMatterSource
lake build
```

Targeted audit: 3901 jobs; full regression: 4358 jobs. All 31 axiom reports
use only `propext`, `Classical.choice`, and `Quot.sound`. No new axioms,
`sorry`, dependency revision, or native-decision trust extension. Existing
SU(6), shared, embedding, and branching audits remain in the full build.
