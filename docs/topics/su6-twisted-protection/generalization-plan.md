# Generalization Plan: Standard-Placement Scalar/Block Obstruction

- Status: completed conditional proof phase; see [result and verification](generalization-result.md).
- Implementation authorized by the subsequent request to proceed autonomously.
- Parent: `su6-twisted-protection`; reuse `proof/su6-twisted-protection`.
- Planning checkpoint: `checkpoint 01`; parent base and integration target are unchanged.
- Intended result: conditional nonzero physical qque coefficient, not an
  SU(6)-wide no-go theorem. No master integration is authorized.

## Decision And Motivation

Keep this as a bounded phase of the existing topic: it has the same SU(6)
protection question and generalizes the two tested scalar/block candidates.
Its standalone plan separates the new proof obligation from their computational
results. A later change of light placement, copy mixing or action class needs
a separate scope decision; it is not an automatic continuation of this plan.

The [C4 test](block-phase-result.md) and [nonliftable C2 test](nonlift-result.md)
both retain nonzero physical qque. The purpose is to identify a whole explicitly
defined class where that failure is structural, without assuming a homomorphic
UV lift or replacing a physical coefficient by a charge signature.

## Frozen Class Of Models

Use a finite Abelian residual group H with discrete topology and a genuine
complex-linear unitary representation U on the actual `15 + bar6 + bar6` UV
space. Fix the standard color/weak embedding and the exact one-generation
light placement of [StandardSMUVFields](../../../GUT/SU6/SelectionRules/Models/StandardSMUVFields.lean).

Supply pointwise functions `a,b,d,c,w,t : H -> Circle` and a pointwise lift
s into SU(6) with the following identities, for every h:

```text
s(h) = diag(c(h) I3, w(h) I2, t(h)),  c(h)^3 w(h)^2 t(h) = 1
E(h) = (a(h) id on 15, b(h) id on first bar6, d(h) id on second bar6)
U(h) = rho(s(h)) E(h).
```

Do not assume s or E is a homomorphism. U must obey its group law on the
original carrier. Inner covariance follows from scalar E and is to be proved;
classification of all covariant U into this form is not part of the task.
In particular, covariance alone does not forbid mixing the two equivalent
bar6 copies. Copy-diagonal scalar E is an explicit restriction.

Use the actual nonzero full-gauge mass
[StandardSMUVMass.mass](../../../GUT/SU6/SelectionRules/Models/StandardSMUVMass.lean)
and require U to preserve it. Its proved radical is exactly the standard
15-dimensional light representation. Preserve the chosen diagonal adjoint
VEV with neutral external scalar action; no complete UV scalar/mass coupling
or complete breaking to precisely SM is claimed. The positive gauge-index
condition is supported by this exact benchmark spectrum, rather than being
used to infer the spectrum of an arbitrary model.

This exact mass/light placement is stronger than the original arbitrary
mass/positive-index interface. A replacement mass may be admitted only through
an independently proved compatible actual-light equivalence; this is a future
adapter, not an implicit hypothesis discharge. Residual Lorentz action is
trivial; quantum exactness remains an external boundary.

## Statement And Proof Route

The candidate theorem says: every model in this frozen class admits a nonzero
SM-cover, residual-H and explicit SL(2,C)-invariant qque exterior functional
on its participating actual light spinor fields. Consequently its residual
symmetry cannot prohibit all dimension-six Delta-B-one coefficients.
There is no conclusion about generated matching coefficients or proton lifetime.

1. **Pointwise cancellation.** Derive from the actual UV branching the
   all-left phases `Q=a c w`, `u^c=a c^2`, `e^c=a w^2`. The right-handed
   dual fields have inverse phases. Therefore
   `(a c w)^2 (a c^2)^-1 (a w^2)^-1 = 1` for each h. This step needs neither
   a field-level group law for E nor s in the unbroken SM group. An arbitrary
   UV compensator is not silently treated as a gauge transformation in K.
2. **Actual radical bridge.** Use the existing full-group branching and
   transported mass radical equivalence to prove those phases on the actual
   Q/u^c/e^c zero modes. U's genuine group law gives the required species
   actions; do not turn the pointwise functions a,c,w into characters without
   proof. Derive radical preservation from mass invariance.
3. **Physical nonzero coefficient.** Transport or extend the existing
   [Lorentz/exterior qque construction](../../proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md)
   to these fields. Prove H invariance by the pointwise identity and retain
   its nonzero alternating witness. The participating field space uses Q and
   the right-handed duals of u^c/e^c, with their spinors; do not substitute
   an untyped fourth exterior power of the all-left radical.
4. **Consumers.** Add an audited SU(6) adapter and explicit comparison of
   hypotheses with both finite candidate calculations. Their computational
   checks alone do not discharge hypotheses of a Lean model instance. A
   conditional class theorem is a valid endpoint without constructing all
   candidate instances; mark that distinction in the result.

Reuse the existing [pointwise comparison](remaining-result.md),
[defect criterion](defect-result.md),
[charge cancellation](../../../GUT/SU6/SelectionRules/StandardBranch/StandardBlockGaugeCancellation.lean)
and [ordered residual tensor](../../../Physics/StandardModel/Gauge/ResidualGaugeTensor.lean)
only where their actual assumptions apply. Neutrality is already largely
available; the new endpoint is its typed actual-light physical nonzero bridge.

## Deliverables, Gates And Stop Conditions

- First implementation step: freeze the exact Lean types and theorem signature
  after checking the existing branching and exterior transport APIs.
- Implement only the pointwise identity, benchmark-light adapter and physical
  nonzero consumer; place reusable mathematics/physics/model work in its layer.
- Add strict transitive audits and aggregate imports. Run focused builds, one
  serialized full `lake build`, layout/link/diff checks and the three existing
  exact candidate/qque scripts. Keep pins and audit allowances unchanged.
- Record the precise result, limitations and verification; update the relevant
  input assumptions ledger and physical dossier only after a proved milestone.
- Accept only a nonzero actual-field exterior functional, not charge neutrality
  or an ordered internal tensor alone. Review and commit on the topic branch.

One bounded route, no alternate-model search. If the existing exterior API
requires genuinely stronger source hypotheses, first check direct pointwise
invariance of its explicit contraction. If an actual-light transport remains
a new foundational prerequisite, record the exact gap and stop for a scope
decision; do not assert the desired theorem or manufacture the missing premise.

Non-goals: arbitrary SU(6) automorphisms, outer/antilinear actions, non-Abelian
residual groups, multiplicity mixing, general flavor spaces, split light
multiplets, all scalar sectors, anomaly cancellation, matching and decay rates.

## Planning Verification

The planning checkpoint passed local links and `git diff --check` without a Lean
rebuild. The subsequently authorized implementation and its precise Lean input
types are recorded in [the result](generalization-result.md). Existing candidate
calculations retain their original computational scope.
