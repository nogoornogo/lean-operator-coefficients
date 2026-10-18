# Common Scale And Two Separate Comparison Gates

The local mass-kernel discrepancy survives every nonzero common complex
factor on the fixed mass matrix. Complete signed generated-coefficient
certification remains open. See the [plan](common-scale-plan.md) and
[verification](common-scale-verification.md).

## Exact Lean Result

[DisplayedKernelComparison](../../../GUT/PatiSalam/Matching/DisplayedKernelComparison.lean)
proves `common_scale_mode_kernel_iff`: for c,d,K nonzero,

```
(c • mass d M 0).mulVec (mode d K) = 0 ↔ M = K.
```

`displayed_common_scale_not_kernel` applies this common-factor invariance to
the existing source dictionary and its displayed heavy entry. Thus multiplying
the entire mass matrix by a nonzero factor, including an overall half or phase,
cannot repair the displayed light-mode mismatch. The zero factor is excluded.
No division by a possibly zero matrix entry is needed.

This is not invariance under independent field rescalings. Such rescalings
change relative matrix entries, kinetic metrics, vertices and the mode's
coordinates together. The source dictionary and its canonical reading remain
fixed; no theorem about arbitrary noncanonical metrics is obtained.

## Two Gates

1. **Local mass comparison:** the fixed dictionary yields
   M=star(yR)*vR/sqrt(2), with a heavy-entry norm different from the displayed
   yR*vR when yR,vR are nonzero. The exact mu=0 displayed light mode fails
   the kernel test for nonzero d, even with a nonzero common matrix factor.
   This bounded comparison is complete. Source admission is an explicit
   reading, not a theorem exhausting every convention.
2. **Complete coefficient certification:** full Grassmann/Lorentz transport,
   arbitrary tau2-conjugate Phi admission, and simultaneous signed source-to-
   registered-coefficient equality remain open. They are not prerequisites
   of the proved local common-factor result. They are needed before claiming
   complete Eqs.(10)–(24) agreement or excluding every coordinated alternative
   convention using mass and vertices together.

Under identical field/coupling/VEV definitions, the displayed formulas have a
local normalization discrepancy. This is not paper-wide refutation. A reading
in which vR changes meaning at Eq.(12) is a possible explanation of notation,
not an established author intention. The earlier conventions and follow-up
files describe their checkpoints; use this result and the
[action translation](action-translation-result.md) for the current local gate.

## Publication And Correction Check (stage 01)

Sources: [arXiv v2](https://arxiv.org/html/2211.02054v2),
[publisher record](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.107.035019),
[published PDF, SCOAP3 copy](https://scoap3-prod-backend.s3.cern.ch/media/files/75913/10.1103/PhysRevD.107.035019.pdf).

The published PDF was inspected visually on pages 035019-2 through -4:

| Target | Published expression | Comparison with v2 |
| --- | --- | --- |
| Eq.(2), adjacent VEV definition | vR=sqrt(2) times neutral chi VEV | Same |
| Eqs.(10),(11) | One chi Yukawa coupling, including neutral and colored terms | Same |
| Eq.(12) | Heavy off-diagonal entry yR*vR | Same |
| Eq.(14) | tan(theta)=mu_up/(yR*vR) | Same |
| Eq.(21) | Selected prefactor 4*vR/sqrt(2) | Same |
| Eq.(24) and following text | Explicit sqrt(2) denominator; approximate mixing mu_up/abs(yR*vR) | Same |

Here `mu_up` means the up-quark mass, not the singlet Majorana parameter.
The publication preserves the relevant displayed normalization pattern.
No all-equation or three-generation comparison is claimed.

The [arXiv history](https://arxiv.org/abs/2211.02054) lists v1 and v2 only.
No linked erratum was found on the publisher record or in searches for the
exact DOI with erratum/correction and for the authors with erratum on the
publisher domain. This is a bounded search, not certification that no
correction exists. Rate, amplitude and numerical-bound rescaling claims from
the supplied review were not adopted.

## Related Convention Tests

The [earlier connection](connection-result.md#what-the-convention-test-establishes)
excludes a common factor with an unchanged Dirac entry in the older component
chart. The present result instead tests the displayed mode against the
canonical source chart. The [multiplet-rescaling result](multiplet-rescaling-result.md)
separately covers simultaneous scalar field/coupling/VEV substitution; it does
not turn the common-matrix-factor theorem into an arbitrary metric theorem.

## Reporting Status

Author notification and any separate public report of the local normalization
discrepancy are undecided. No author response or external notification is
recorded. Subsequent numerical calculations, rates and bounds have not been
verified; no consequence for their numerical values is certified. These
reporting decisions are separate from the verified local comparison.
