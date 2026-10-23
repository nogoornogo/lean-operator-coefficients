# Results And Application Boundary

The frozen A–D contract is proved. The additive API is
[`Math.DerivativeProhibition`](../../../Math/RepresentationTheory/DerivativeProhibition.lean).
It consumes the existing `DerivativeInterface.Input H U`; its coefficient
space and source quotient are unchanged. This is a theorem-to-input
connection, not a classification of admissible field theories.

## Conditions On The Actual Quotient

For an input P with stable relations T, write Q = U/T. `Forbids P` means
every admissible coefficient is zero. `Allows P` means one is nonzero.
The existing inverse equivalence identifies these predicates with vanishing
or nonvanishing of equivariant linear maps from Q to the trivial scalar target.

| Available input evidence | Proved criterion |
| --- | --- |
| Q is nontrivial and its action is the scalar z(g) | `scalar_iff`: prohibition iff some g has z(g) different from one |
| The same scalar action, without a nontriviality instance | `scalar_supported_iff`: prohibition iff nontrivial Q implies such detection |
| Scalar action already proved on U | `ambient_scalar_supported_iff`: descends the scalar action and applies the guarded criterion |
| Actual quotient representation is semisimple | `no_shared_iff`: prohibition iff it shares no irreducible constituent with the trivial target |
| An indexed family of actual scalar-action inputs | `all_scalar_supported_iff`: every selected input is forbidden iff every nonzero selected quotient is detected |

No finite-dimensionality is needed for these generic statements. The group
is exactly the supplied H. Applying a residual-only test to a physical
problem requires local symmetry to have been accounted for in its source;
scalar action on a full Lorentz representation is not inferred from field
charge labels. Semisimplicity is an explicit alternative hypothesis, not a
consequence of arbitrary group action.

The family theorem quantifies over an arbitrary family and selector. It
does not construct a decomposition of a nonlinear EOM quotient, enumerate
its nonzero support or give a finite search cutoff. `zero_grade_iff` recovers
the original nonderivative prohibition predicate for the graded entry at
derivative degree zero, before adding EOM.

## Adding Relations And Selecting Targets

`extend P T hT` adds a specified stable relation submodule. Its coefficient
map `forgetRelations` is injective and preserves evaluation. Prohibition
before adding relations implies prohibition afterwards; allowance afterwards
implies allowance beforehand. `transport` separately transports prohibition
through a supplied coefficient equivalence.

`TargetForbids P V` says every global coefficient vanishes on an invariant
selected subspace V. Prohibition of the selected input implies this property.
The converse in `target_selected_iff` requires surjectivity of the actual
coefficient restriction map. `target_charge_detected` and `target_no_shared`
retain that premise, plus the nonzero/scalar or semisimplicity evidence
needed for their respective selected-source tests.

This extension premise cannot simply be removed. The
[unipotent control](../../../Math/RepresentationTheory/DerivativeSelectionCounterexample.lean)
acts on complex pairs by (x,y) going to (x+t*y,y). Every global invariant
functional vanishes on the fixed x-axis, while that axis itself has a
nonzero invariant coefficient. The restriction is proved nonsurjective.
This is a generic group-action counterexample, not a claim that the physical
Lorentz consumer has the same extension obstruction.

## Actual Controls And Parameter Restriction

The [Math controls](../../../Math/RepresentationTheory/DerivativeProhibitionControls.lean)
include a neutral nonzero coefficient and a nonzero scalar-action quotient
detected by the unit minus one. In the existing actual one-direction,
one-species quadratic jet source, an explicit reduction functional survives
IBP. Adding the full free-EOM kernel makes the quotient zero. Thus neutral
prohibition alone does not require a nontrivial charge, and prohibition
after adding equations does not imply prohibition before them. These
controls use actual relation modules, not an assumed rank table.

The [Lorentz scalar consumer](../../../Physics/FieldTheory/Jets/ScalarProhibitionConditions.lean)
uses the existing full input with equation box phi + lambda times phi cubed,
arbitrary complex lambda and the actual SL(2,C) action. The wave term is
proved to be a divergence. Consequently every admissible global coefficient
f obeys lambda times f(phi cubed) = 0. If f(phi cubed) is nonzero for some
global coefficient, lambda must be zero. For nonzero lambda the cubic
evaluation vanishes, also on the existing selected wave/cubic input.

This is an exact necessary parameter condition for that coefficient witness.
It does not prove existence at lambda zero, prohibition of the entire scalar
coefficient space, or an interaction/rate prediction. The calculation uses
the full EOM/IBP relations, without assuming a homogeneous on-shell grading
or that all selected coefficients extend globally.

## Settled Stop

The [verification](verification.md) records the strict audits and repository
gates. Existing public nonderivative APIs and derivative factories remain
unchanged. C1–C5 of the previous literature comparison retain their documented
gaps. A physical input classification, arbitrary support solver, complete
SMEFT basis or the missing literature dictionaries would require separately
bounded work. None is a premise of the proved conditions here.
