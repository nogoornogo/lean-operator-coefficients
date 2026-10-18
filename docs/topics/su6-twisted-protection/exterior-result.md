# Covariant Exterior And Support Bridge

## Result

[AutomorphismCovariantExterior](../../../Math/RepresentationTheory/AutomorphismCovariantExterior.lean)
constructs the exterior action from actual field covariance at every degree.
A supplied unsupported-input relation span stable under local and residual
actions gives a supported quotient carrier. `supportedAction` derives
covariance on that quotient; no new covariance assumption is imposed there.

`ofGenerators` builds the relation span from an independently specified set
of pure exterior inputs. Preservation of that set under each field action
implies stability of its span. This is a sufficient generator-level test,
not a claimed necessary classification of all stable relation submodules.

`Input` independently specifies residual-equivariant functionals on the original
exterior carrier which are locally invariant and vanish on unsupported inputs.
`supportEquiv` descends and reconstructs them through the support quotient;
`inputEquiv` further descends through local coinvariants. Both inverses are
proved. `input_forbidden_iff` says these original supported functionals all
vanish exactly when the constructed residual Hom all vanishes.

The construction respects algebraic fermionic alternation through the actual
exterior power, including repeated-input zero relations. No contraction basis,
dimension count, semisimplicity or finite-dimensionality is used in the Math
bridge. A scoped elaboration allowance of 800,000 heartbeats is used for the
support equivalence; it changes no assumptions or trust boundary.

## Actual SU(6) Light-Field Specialization

[CovariantFourFermion](../../../GUT/SU6/SelectionRules/Models/CovariantFourFermion.lean)
uses the actual mass radical and derived residual action of the covariant model.
It instantiates degree four without an assumed exterior-action certificate.
`Support`, `Input`, `inputEquiv`, and `input_forbidden_iff` expose the support
and complete gauge/residual functional criterion on actual light vectors.

The low-energy support is supplied independently. In particular no assumption
that a noncommuting residual action preserves the original BNV species support
is hidden inside the proof. That preservation must be certified using the
actual field action, for example with `ofGenerators`.

## Scientific Limits And Next Candidate Problem

This completes the exterior/support bridge, not the full physical dimension-six
BNV comparison. The actual-radical specialization includes K gauge invariance
and H residual invariance, but it does not construct the Lorentz spinor factor.
It does not instantiate the supplied relation span with the ten signed SM
species or prove a new four-family comparison under arbitrary normalizing
species actions. Calling its gauge-only fourth-exterior functionals full proton
operators would be incorrect.

The generic Math result can include a local gauge/Lorentz group when its full
field action and covariance are provided. Before using it for a physical
candidate, supply:

1. Actual SU(6) matter/scalars, automorphism action, unbroken embedding and VEV.
2. Positive and residual-resolved SM target certificates on actual light modes.
3. The spinor field presentation and its local/residual covariance.
4. An independently defined dimension-six BNV support and preservation proof.
5. A proof that the resulting residual Hom is zero, or a nonzero counterexample.

No protecting candidate or automatic solution of these constraints is claimed.
The earlier inner-lift cancellation still applies when its certificates hold.
The outer or non-split action search remains a separate scientific endpoint.

## Verification

Persistent strict transitive audits:
[exterior](../../../Math/RepresentationTheory/Audit/AuditCovariantExterior.lean)
and [SU(6) specialization](../../../GUT/SU6/SelectionRules/Audit/AuditCovariantFourFermion.lean).
Commands and final results are recorded in the topic overview. No axiom
allowance or dependency/toolchain pin is changed.
