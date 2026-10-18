# Actual SM compact extraction with a Weyl literature input

The three application obligations left after `checkpoint 01` are now proved:
a combined compact action and coefficient comparison, joint continuity, and
an actual finite integer inverse-torus-character presentation. The final
kernel dimension/rank/local support statements retain only the explicit
Weyl torus-reduction input introduced in the [previous result](weyl-input-results.md).
They remain conditional statements, not a Lean proof of Weyl integration.

## Combined actual compact action

[SMCombinedCompactAction](../../../Physics/StandardModel/Operators/SMCombinedCompactAction.lean)
acts on the existing ten signed field carriers with the compact gauge group
and independent left/right SU2 factors. The gauge component acts on the gauge
slots, each spin component on its appropriate chirality, and the flavor
multiplicity slots are fixed for this local comparison. The actual statistical
source and Higgs constituent are retained at arbitrary degrees.

`field_gauge`/`field_spin`, `source_gauge`/`source_spin` and
`action_gauge`/`action_spin` identify the factor restrictions with the existing
local gauge and independent-spin actions. The reusable
[ProductInvariantCoefficients](../../../Math/RepresentationTheory/ProductInvariantCoefficients.lean)
constructs invariant coefficients as simultaneous fixed coefficients from
these proved restrictions. `coefficientEquiv` therefore identifies the
combined invariant space with the existing `LocalSpace`; no comparison premise
is left supplied. The previously proved `kernelEquiv` connects that space to
the actual original finite local constraint kernel.

## Proved continuity

[BasisActionContinuity](../../../Math/RepresentationTheory/BasisActionContinuity.lean)
constructs joint continuity on a finite Hilbert copy from continuous basis
coefficients. Tensor products, duals and continuous restrictions preserve
this condition. `source_copy_continuous` descends continuity through the actual
statistical source's pure span and onto map. It does not presume an ordered
tensor basis is a basis of the statistical source.

[SMCombinedCompactContinuity](../../../Physics/StandardModel/Operators/SMCombinedCompactContinuity.lean)
proves the required coefficients for all ten species from matrix entry
continuity, hypercharge phases, tensor products and duals. Its source model
is the Hilbert copy of the actual source. The Higgs model uses TauCeti's
continuous symmetric-power model with its retained hypercharge twist.
`equiv`, `continuous_model` and `coefficientEquiv` construct the full analytic
model, its joint continuity and the actual coefficient comparison. Original
algebraic carriers receive no global orphan topology/norm instances.

## Constructed finite integer presentation

[FiniteTorusPresentation](../../../Math/RepresentationTheory/Characters/FiniteTorusPresentation.lean)
first proves continuity of every active unitary torus eigencharacter from a
nonzero eigenvector and a nonzero finite basis coordinate. The existing circle
character-lattice theorem then supplies its integer exponent vector. Full
active weight spaces give finite integer multiplicities and the proved actual
character expansion. The proof uses the existing full-spectrum decomposition,
not a supplied rank or weight-multiplicity table.

For an arbitrary jointly continuous finite-dimensional representation and a
continuous finite torus homomorphism, the inverse restriction is unitarized
using the existing `FiniteBasisUnitaryModel`. `inverseCoefficients` and
`inverse_presentation` construct the finite integer Laurent presentation of
the actual inverse character. This is a noncomputable construction using
classical choices and torus weight-space dimensions. It is not an executable
recurrence for the known species weights and does not by itself compute
concrete numerical multiplicities. No kernel dimension is used to define it.

[SMCompactTorus](../../../Physics/StandardModel/Operators/SMCompactTorus.lean)
constructs the continuous six-circle homomorphism explicitly. Coordinates are
color z0,z1; weak z2; left spin z3; right spin z4; hypercharge z5. The color
matrix is `diag(z0,z1,(z0*z1)^-1)`; membership, multiplication and continuity are
proved. Positive-root coordinates supplied to the extraction input are

    alpha = (1,-1,0,0,0,0)
    beta  = (1, 2,0,0,0,0)
    alpha+beta, (0,0,2,0,0,0), (0,0,0,2,0,0), (0,0,0,0,2,0).

The color coordinates correspond to diagonal ratios z0/z1 and z1/z2, with
z2=(z0*z1)^-1. Maximal-torus/root classification in compact Lie theory belongs
to the documented specialization of the external reduction law; no Lean
root-system classification or maximality theorem is asserted here.

## Actual conditional multiplicity and support

[SMCompactMultiplicity](../../../Physics/StandardModel/Operators/SMCompactMultiplicity.lean)
constructs `polynomial` and proves `presents` for every ordered content p,
Higgs constituent m and hypercharge index delta. Its `Input` is precisely
`TorusReduction` for this fixed compact model, torus, monomials and roots.
No compact comparison, continuity or presentation is supplied to its final
theorems as an extra hypothesis. Only this external mathematical reduction
law remains a parameter.

`multiplicity` is the finite-root extraction of the constructed polynomial.
Under `Input`, `kernel_dimension_int` and `kernel_dimension` identify it with
the actual kernel dimension; `nonnegative` prevents negative-value truncation;
`rank_formula` subtracts it from the all-content symbolic column count;
`local_allowed_iff` proves local support exactly when it is positive.
Degrees/counts remain symbolic, with the empty word and all mixed chiralities
included. No fixed-degree numerical dispatch, CSV update, epsilon test or
custom axiom is used.

## Exact completion boundary

Task III's application-side comparison/continuity/presentation bridge is
complete under the user-authorized Weyl literature-input boundary. The Weyl
input itself is not proved or instantiated in Lean. These audits prove the
conditional implications and all the separately constructed application data.

Computable weight recurrences and numerical all-content ranks remain separate;
the spectral polynomial is finite and mathematically constructed, but uses
classical choices. This module proves local support. The subsequent
[q/l consumer](ql-extraction-results.md) uses the already proved scalar cyclic
residual separation to close the existing q/l support iff. Other residual
representations/classes still require their own invariant conditions. Original full-residual Higgs support
continues to use its existing residual coefficient predicate. No physical
matching/amplitude/rate or new foundation/dependency is introduced.

The later [computable presentation](../sm-computable-characters/results.md)
constructs explicit simultaneous slot weights and executable reference terms
with an unconditional `Presents` theorem. Its actual kernel/support consumers
use this same Weyl input; large numerical evaluations remain bounded separately.

Persistent audits: `AuditFiniteTorusPresentation` and `AuditSMCompactMultiplicity`.
See [verification](verification.md) and the [authorized continuation](weyl-input-plan.md).
