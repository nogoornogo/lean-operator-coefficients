# SU(5) final assembly and quotient tensors

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The retained
positive-generation SU(5) matter class supplies the scoped selection-rule
witness and quotient-invariant ordered tensors.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

SU5-5: `LEAN-CHECKED`, stage 01. See the
[statement and scope](../SU5_SELECTION_RULE.md). This completes the
five-milestone scoped SU(5) roadmap, not its deferred physics extensions.

## 2. Inputs And Conclusion

The model has a positive generation count and an ordinary Abelian residual action on the specified matter.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Kernel-trivial field actions descend the supported tensors to the SM quotient;
the source witness refutes universal charge prohibition.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declarations

| Module | Public interface |
| --- | --- |
| [RepresentationDescent](../../../../../../Math/RepresentationTheory/Decomposition/RepresentationDescent.lean) | `descend`, `descend_comp`, `descend_invariant`, `kernel_dual`, `kernel_tensor` |
| [SupportedQuotient](../../../../../../GUT/SU5/SelectionRules/SupportedQuotient.lean) | `field_kernel`, `fieldAction_cover`, `fieldAction_val`, `qque_kernel`, `duql_kernel`, `quotientQQueAction_cover`, `quotientDuqlAction_cover`, `qque_quotient_invariant`, `duql_quotient_invariant` |
| [SelectionRule](../../../../../../GUT/SU5/SelectionRules/SelectionRule.lean) | `FieldSupported`, `SlotsSupported`, `slotCharacter`, `ForbidsEverySupportedDeltaBOne`, `OperatorWitness`, `witness_exists`, `scoped_no_go`, `Model.selection_rule_obstruction`, `oneGeneration`, `oneGeneration_result` |
| [AuditSelectionRule](../../../../../../GUT/SU5/Audit/AuditSelectionRule.lean) | Persistent scope, finite-action, quotient, and contragredient controls |

Namespaces are `GUT.RepresentationDescent`, `GUT.SU5.SupportedQuotient`,
`GUT.SU5.SelectionRule`, and `GUT.SU5.AuditSelectionRule`.

`RepresentationDescent` uses mathlib's `Representation.asGroupHom` and
`MonoidHom.liftOfSurjective`, then forgets the units. This factors an actual
representation through a surjection only after its kernel condition has
been supplied. `SupportedQuotient` proves that condition from the actual
field action; it is not an assumed SM realization certificate. Descent
preserves the tensor spaces and forms, so their previously proved
nonvanishing is unchanged. The two covering-pullback equalities and
`fieldAction_val` check compatibility with the original actions.

`Model` contains exactly a positive generation count and an arbitrary
`OrdinaryAction` on that matter. `OperatorWitness` is constructed as an
output. It carries one common selection of five actual field embeddings,
both trivial operator characters, and both nonzero quotient-invariant
ordered forms. Universal prohibition allows independent per-slot charge
assignments; the witness specializes to a suitable constant assignment.

## 6. Scope And Limitations

No arbitrary SU(5) Lagrangian classification, nonzero Wilson coefficient or physical amplitude is asserted.

## 7. Sources And Verification

The [scope dossier](../SU5_SELECTION_RULE.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Persistent Controls

- Zero generations have no field injection and satisfy universal prohibition
  vacuously. Thus the endpoint's positivity premise has actual content.
- The one-generation model exists for every Abelian residual group.
- The order-two generation-swap source has an explicitly chosen odd `10`
  mode and a trivial `bar5` mode. Their actual fields give neutral signatures
  and nonzero invariant tensors; this is not only an abstract existence test
  that might select a trivial character.
- An even Q in one slot and an odd Q in another are both supported in the
  same source but produce a nontrivial total character for that choice.
- The nonidentity compensated kernel element is invisible on both tensors.
- Dual action at phase `i` gives `-i`, testing inversion beyond two-torsion.
- Existing negative IR-charge and incompatible-within-one-10 controls are
  retained. They do not assert that family-dependent actions are impossible.
- Lean's transitive module environment rejects any SU(6) import.

```sh
lake build GUT.SU5.Audit.AuditSelectionRule
lake build
```

Targeted audit: 3906 jobs. The final audit has 28 axiom reports, each using
only `propext`, `Classical.choice`, and `Quot.sound`; the imported source and
shared audits are checked too. No `sorryAx`, new axioms, or native-decision
trust extension. Full regression: 4362 jobs. Dependencies/toolchain remain
pinned and existing SU(6) theorem interfaces are unchanged.
