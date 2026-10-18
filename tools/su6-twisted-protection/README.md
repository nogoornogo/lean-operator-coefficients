# Standard-block C4 candidate audit

Run from the repository root, with Python 3.8+ and no extra packages:

```sh
python3 tools/su6-twisted-protection/audit_block_phase.py
python3 tools/qque/audit_one_generation.py
```

Six tests check the explicit 27-component candidate: residual order, inner
covariance on all matrix units, adjoint vacuum fixedness and standard-block
preservation, symmetric mass/rank/light dictionary, all twelve standard gauge
Lie generators, and the nonzero one-generation Lorentz/Grassmann qque
polynomial. Integers, Gaussian integer pairs, fourth-root exponents and exact
fractions are used; no numerical approximation or sampling. Negative controls
alter the second-copy phase in the mass test and the electron phase in qque.

The contraction is reused from [the qque audit](../qque/README.md), whose
normalization and independent full alternation test remain unchanged. Rerun
both commands if basis, mass, phase, contraction or sign conventions change.
See the [frozen plan](../../docs/topics/su6-twisted-protection/block-phase-plan.md)
and [result/scope](../../docs/topics/su6-twisted-protection/block-phase-result.md).

These finite calculations are not Lean certificates. Lie-generator checks
are not a separately formalized full-group covariance/invariance proof. No UV
scalar/mass coupling, anomaly calculation, generated interaction or decay rate
is supplied.

## Nonliftable UV C2 Candidate

```sh
python3 tools/su6-twisted-protection/audit_nonlift.py
```

Six additional exact tests reuse the basis/mass/contraction utilities and
check the candidate `s=diag(i,i,i,-i,-i,-i)`, with external phase +i on both
dual-six copies. The finite action on matter has order two, while its UV
inner automorphism has no homomorphic SU(6) lift. A 36-variable centralizer
system of rank 35 proves completeness of the six central corrections; all
six fail the lift square condition. The removed-action defect is visible,
but the physical qque polynomial still survives. Negative controls cover
a liftable inner generator and a changed electron sign.

Rerun all three commands when shared conventions change. The
[result](../../docs/topics/su6-twisted-protection/nonlift-result.md) explains
the distinction between UV nonliftability and the trivial automorphism of
the chosen SM subgroup, and records the remaining physical boundaries.

## Standard SM block probes

Run `python3 tools/su6-twisted-protection/check_sm_block_probes.py` from the
repository root. Python standard library only; three unittest checks use exact
integer matrices. The script scans all 720 coordinate permutations with signed
SU(6) representatives, checks four embedded color/weak probes and records
12 passing / 708 failing representatives. It checks the new (0,3) witness's
order four and cross-entry -1. This is a finite probe screen, not a classification
of arbitrary normalizers, phases, scalar vacua, masses or protecting models.
See [sample results](../../docs/topics/sm-support-and-lfv-decomposition/outside-class-sample-results.md).

## Unequal S3 qque tensor controls

Run `python3 tools/su6-twisted-protection/check_s3_qque_tensor.py` from the
repository root. The Python standard-library signed-orbit enumeration checks
all six S3 elements, ordered versus symmetric Q-pair coordinates and three
fixed u/e copies. Three tests pass: single sign ordered/symmetric dimensions
9/0, double sign 18/18, and zero Q/sign single-factor overlap. These supplement
Lean zero/nonzero certificates; they are not Lean dimension premises or UV
model tests. See [sample results](../../docs/topics/sm-support-and-lfv-decomposition/sm-preserving-sample-results.md).
