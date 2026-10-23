# Mixed Jets, Linear Actions And EOM: Extension Assessment

Status: retained planning assessment. A/B were subsequently authorized and
completed under the [mixed contract](mixed-implementation-plan.md); see their
[proved result](../../proof/current/core/Math/MIXED_JET_IBP.md). C–E were subsequently
authorized and implemented under the
[direction/Lorentz/EOM contract](direction-lorentz-eom-plan.md). The completed
[scalar contract](implementation-plan.md) and its proof baseline remain intact.
Work is recorded on `proof/derivative-ibp`, whose integration target is `master`.

## Recommendation And Estimate

The proposed mixed-statistics → Lorentz → EOM order is reasonable, with two
refinements: first extract arbitrary **internal** linear covariance, then split
linear action on **derivative directions** from its actual Lorentz specialization.
This avoids extending the current component-permutation presentation twice.

Use one planning unit, **U**, for the scope of the completed scalar package:
unbounded generators, graded derivatives, finite fixed grades, actual IBP range,
inverse coefficient descent, a complete nonzero quotient consumer and audits.
The ranges below are engineering judgments about relative work, not measured
calendar time, agent turns or performance guarantees. They include source
bridges, one bounded consumer and verification; they exclude general operator
enumeration and physical amplitude results.

| Stage | New foundation and reuse | Estimated scope |
| --- | --- | --- |
| A. Internal linear action | Lift arbitrary field representations to jets; prove the scalar coordinate/source bridge, grade stability and derivative covariance. Reuse free-algebra functoriality and quotient/Hom descent. | 0.5–1.5 U; medium |
| B. Mixed Bose/Fermi jets | Assemble the even derivative on exterior ⊗ symmetric jets; prove joint grading, finite grades, actual coefficient-source equivalence and IBP descent. Reuse existing factor derivations and derivative-free mixed completeness. | 2–4 U; large |
| C. Linear action on directions | Construct the symmetric-power jet action and covariant current; prove divergence equivariance and relation stability. | 1–2 U; medium to large |
| D. Actual Lorentz action | Connect C to the existing SL(2,ℂ), Weyl and four-direction conventions; certify a scalar consumer and a Weyl transformation check. | 1–3 U; high transport uncertainty |
| E. Free massless scalar EOM | Construct derivative-closed on-shell jets, induced derivatives and the combined EOM/IBP source quotient; certify one complete quotient. | 1–3 U; large |

A–E total roughly **6–14 U**. A free Weyl-EOM extension is a further **1–3 U**
planning allowance after the scalar gate. Interacting or gauge EOM are outside
these estimates. If a bridge fails, the upper range is a reassessment point,
not authority to begin another foundation or raise resource limits.

Recommended path: **A → B → C → D → E**. C can be prototyped on scalar jets
after A without waiting for all of B. A one-direction EOM regression can also
be explored early, but does not complete the four-dimensional Lorentz/EOM gate.
The completed A/B package now supplies the representation and grading bridges.
The user subsequently authorized C → D → E without a separate estimate stop
after D. The relative ranges above remain the original planning estimates,
not measured implementation costs. The contract and result dossiers own the
implemented statements and verification.

## A — Internal Linear Covariance

The current `relabel` action permutes components and fixes derivative directions.
Replacing its type by a general linear map does not supply the required proofs.
The proposed common interface is a field module for each statistics sector,
its unbounded jet-generator module and functorial linear actions. Fix whether
generators represent fields or coordinate functions before selecting a dual
action; retain the current coefficient-as-linear-map convention explicitly.

New obligations are a two-way connection to the current scalar polynomial
presentation, preservation of joint grades and commutation with total
derivatives. Local and residual groups remain arbitrary commuting actions;
compactness and semisimplicity are not needed for the Hom descent. Finite
field fibres and finitely many directions enter only the finite-grade claims.

Acceptance: a genuine non-permutation action (for example a shear), covariance
on all jets, inverse transport of coefficient maps, and recovery of the
degree-zero field representation. Keep this interface reusable by B rather
than building a second unrelated scalar implementation.

## B — Mixed Jets And Their Actual Source

Use one exterior algebra on **all** odd jet generators, tensored with the
symmetric algebra of the even generators:

\[
 A=\Lambda(J_F)\otimes\mathrm{Sym}(J_B).
\]

An ordinary tensor product of separately constructed species exterior algebras
does not automatically provide the required cross-species fermion signs.
Spacetime differentiation is an **even** derivation:
`D(ab) = D(a)b + aD(b)`, including when both factors are odd. Odd reordering,
not differentiation, supplies the statistics sign.

Physlib already supplies even derivations on exterior and symmetric algebras,
including generator formulas, commutation and covariance. New work remains:

1. Assemble the tensor derivative and the `(nF, nB, d)` grading; prove finite
   fixed grades without truncating the jet tower.
2. Connect these grades in both directions to the actual statistics-constrained
   coefficient source used by the derivative-free theorem; recover it at `d=0`.
3. Construct divergence ranges and their stable local/residual actions, then
   reuse the general coefficient descent on this actual source.

IBP moves derivatives between factors. A decomposition by derivative
distribution cannot simply be carried through the quotient as independent
sectors. Underlying species content remains usable when the action preserves it.

A proposed one-direction consumer has one even field `φ` and one odd field `ψ`,
with `(nF,nB,d)=(2,1,2)`. Its candidate source generators are
`φ₁ ψ₀ ψ₁` and `φ₀ ψ₀ ψ₂`; differentiating `φ₀ ψ₀ ψ₁` gives their sum because
`ψ₁²=0`. Acceptance requires proving the full source and current spans, the
entire relation range and a surviving quotient class. These were proposed
checks at the assessment checkpoint and are now proved in the completed A/B
package. A generic Leibniz theorem alone is not this stage's endpoint.

## C — Directions And Currents Must Transform Together

For spacetime actions, derivatives generally mix:

\[
 \rho(g)D_i=\sum_j c_{ji}(g)D_j\rho(g).
\]

Thus componentwise commutation with every `D_i` is the wrong acceptance gate.
For a current with components `J_i`, the compatible action has components
`(g⋅J)_j = ∑ᵢ c_{ji}(g) ρ(g)J_i`. This makes divergence equivariant and its
range stable. Whether `c` is a vector or a dual matrix depends on the chosen
derivative convention; it must be derived rather than called contragredient
without that convention.

An abstract interface uses a derivative-parameter module `P` and an intertwiner
`D : P ⊗ A_previous → A_target`. Order-`r` jet generators use
`Symʳ(P) ⊗ F`. New work connects this construction to multi-index jets, fixes
basis normalization, proves the current formula and transports IBP descent.
A non-diagonal direction change at order two should test transpose and binomial
coefficients. Restriction to Lorentz transformations is a later specialization;
a general direction action alone supplies no invariant metric.

## D — Lorentz Specialization Without Rebuilding The Group

The repository already has actual algebraic left/right Weyl actions of
`Matrix.SpecialLinearGroup (Fin 2) ℂ`, including the conjugate right action and
invariant epsilon forms. Physlib supplies the map to the Lorentz group and a
covariance interface for families of derivatives. Basic SL(2,ℂ) and Weyl
representation theory therefore need not be rebuilt.

New work fixes the Minkowski signature, vector/dual convention, connected
Lorentz cover and its relationship to the existing Weyl actions, then connects
these to C and the actual jet source. The first consumer should prove scalar
metric contraction and a Weyl derivative transformation, with equivariant
IBP descent. Disconnected parity/time-reversal actions, full Lorentz
invariant-ring classification and general EFT counting are separate endpoints.
No compact-group averaging assumption is introduced for the actual Lorentz group.

The inspected full Physlib SM jet/Lorentz closure is not a verified import
baseline here. Its large elaboration limits are a compatibility risk, not a
template for changing this project's limits. Prefer a narrow generic interface
or attributed adapter, and stop for reassessment if its necessary closure fails.

## E — Start With Homogeneous Free EOM

The first EOM should be `□φ=0` for a free massless scalar, with **all derivative
descendants**. Construct the quotient jet-generator module, prove derivative
and Lorentz stability, and induce its free algebra and derivatives. Compare
this presentation with the algebraic EOM relations before claiming coefficient
completeness on shell. Existing commutative derivation descent helps once
kernel stability is proved; it does not prove that stability.

The combined quotient requires the EOM relation submodule plus the divergence
range, or an EOM algebra quotient followed by its induced IBP quotient.
**The IBP range is generally not an ideal.** Ideal-closing it would impose
extra relations. Setting only a finite selection of higher jets to zero also
does not establish a derivative-closed EOM system.

An early regression can reuse the current one-direction quadratic example:
EOM sets `φφ″` to zero, and its existing IBP relation then sets `(φ′)²` to zero.
Its off-shell quotient of dimension one should become zero. This expectation
still needs a complete Lean source/range proof. In four dimensions, the wave
equation removes traces; it does not eliminate the entire higher-jet tower.

Mass terms mix derivative grades. Nonlinear EOM can also mix field counts, so
the present fixed `(nF,nB,d)` grades no longer define the same quotient problem.
They require a chosen engineering/EFT grading or filtration, model and coupling
conventions. Weyl EOM additionally needs spinor contractions and odd-generator
relations; commutative `Ideal` APIs alone do not supply the mixed construction.
Gauge-covariant derivatives, curvature and Bianchi relations require another
scope decision. None is included in E or its estimate.

This endpoint is a formal algebraic EOM/IBP coefficient quotient. Derivation
from a Lagrangian, equivalence of integrated actions or S-matrix equivalence
would each require additional statements and application conditions.

## Evidence And Implementation Gates

Already checked in the completed project baseline:

- [Scalar jets/IBP](../../proof/current/core/Math/SCALAR_JET_IBP.md) and generic
  [mixed completeness](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md).
- [Adapted symmetric derivations](../../../Math/LinearAlgebra/PhyslibSymmetricDerivations.lean)
  and the imported exterior fragment, with the persistent algebra-connection audit.
- [Weyl actions](../../../Physics/FieldTheory/Spinor/WeylSpinor.lean) and
  [their paired-action connection](../../../Physics/FieldTheory/Spinor/WeylIndependentAction.lean).

Additional source inspection, **without a new compile or axiom audit**:

- Pinned Physlib mixed jet derivative, Lorentz derivative interface, local
  power-series jets, and QED equation definitions; see the
  [source register](references.md#extension-assessment-source-inspection).
- TauCeti symmetric grading/graded maps and `SymmetricAlgebra.derivationOfEnd`
  with naturality and preservation of ordinary generator-count degree. These
  do not by themselves supply the required joint derivative grading.
- Mathlib `Derivation.liftOfSurjective` in
  `Mathlib/RingTheory/Derivation/Basic.lean`: commutative-algebra descent under
  an explicit kernel-stability premise. TauCeti's
  `RingTheory/Derivation/Ideal.lean` has useful ideal lemmas, not a ready-made
  differential-ideal/EOM quotient construction.

The existing R1/R2 literature guides the distinction between off-shell IBP,
linearized EOM and physical interpretation. It is not a completeness premise.
No matching complete EOM/IBP coefficient quotient was found in the bounded
source inspection; this is not a claim about every Lean library.

Before implementing any stage, freeze its precise modules, action and dual
conventions, theorem statements, finite-grade hypotheses, concrete consumer,
resource envelope and failure stop in a separate implementation contract.
Require focused builds, persistent strict transitive audits, full `lake build`
and the existing layout/documentation gates. Do not accept merely assumed
stability, a supplied relation matrix or a generic quotient wrapper in place of
the stage's source bridge. A failed compatibility or semantic bridge yields a
documented stop and revised estimate, not a silently enlarged foundation.

## Authorized Formal First Variation

The explicit follow-up instruction reopened the formal algebraic part of the
previous variational deferral. The [completed child result](../formal-first-variation/results.md)
derives normalized scalar and matrix Yang–Mills first variations, explicit
boundary currents, actual epsilon coefficients and exact differential EOM
ideal bridges. The generic supplied-EOM interface remains available. Analytic
integrated actions, boundary conditions and quantum or higher-order
field-redefinition equivalence remain outside this result. The verified child
is unmerged into its recorded gauge/engineering parent.

## Settled Theorem Endpoint

The user accepted the recorded derivative/IBP/EOM theorem endpoints and
authorized [master integration](master-integration.md). Input-interface parity
and usability are reserved for a separate topic. General Lagrangian input is
a later optional extension. Neither is an unfinished proof obligation of the
completed contracts. Analytic actions and higher-order or quantum equivalence
remain outside the endpoint.
