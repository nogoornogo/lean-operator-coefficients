# Source Register

The [preflight](../dgt-quarticity-mixed-requests/follow-up-candidates.md) pins
both primary papers and inspected locations:
Dev–Mohapatra arXiv:1504.07196v2, Sec.II Eq.(1), Sec.III Eqs.(3)-(5);
Ma–Pollard–Srivastava–Zakeri arXiv:1507.03943v2, pp.2-3 Eqs.(1)-(6).
Printed phases/actions and nonzero local/statistics semantics are proof
obligations, not consequences of paper statements.

- [Mixed requests](../../../Math/LinearAlgebra/MixedSelectionRequests.lean).
- [B/L input](../../../Physics/StandardModel/Operators/ComposableBLSupport.lean).
- [Six-quark coordinates](../../../Physics/StandardModel/Operators/SixQuarkFlavorCoordinates.lean)
  and [residual/statistics domain](../../../Physics/StandardModel/Operators/SixQuarkFlavorResidualHom.lean).
- [Local admissible coordinates](../../../Physics/StandardModel/Operators/SixQuarkSpeciesQuotient.lean).
- [Quarticity actual adapters](../../../Physics/StandardModel/Operators/QuarticityAdapters.lean):
  epsilon exterior construction reused; do not equate Z4/real eta with Z3/complex chi2.

## Primary Sources and Implemented Consumers

- Dev and Mohapatra, *A TeV Scale Model for Baryon and Lepton Number Violation
  and Resonant Baryogenesis*, [1504.07196v2](https://arxiv.org/abs/1504.07196v2),
  Sec. II Eq.(1), Sec. III Eqs.(3)–(5). Printed parity and distinct down-flavor
  requirement motivate the bounded restriction; generated matching is not certified.
- Ma, Pollard, Srivastava and Zakeri, *Gauge B-L Model with Residual Z3 Symmetry*,
  [1507.03943v2](https://arxiv.org/abs/1507.03943v2), pp.2–3 Eqs.(1)–(6),
  especially the common residual omega phase and chi2 NN coupling in Eq.(5).
- [Parity and LLHH](../../../Physics/StandardModel/Operators/DevMohapatraParity.lean),
  [six-quark witness and request](../../../Physics/StandardModel/Operators/DevMohapatraSixQuark.lean),
  [Ma actual adapters and request](../../../Physics/StandardModel/Operators/MaZ3Mixed.lean),
  [strict audit](../../../Physics/StandardModel/Operators/Audit/AuditNonSusyMixedCandidates.lean).
