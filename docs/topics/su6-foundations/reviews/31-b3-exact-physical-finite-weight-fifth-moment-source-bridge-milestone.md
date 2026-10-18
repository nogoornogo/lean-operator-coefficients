# B3 exact physical finite-weight fifth-moment source bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B3 exact physical finite-weight fifth-moment source bridge milestone
- Local-model role: none

### Audit result

`GUT/SU6/Characters/PhysicalFifthMomentBridge.lean` now kernel-checks the missing exact
finite-weight calculation in the continuous-unitary B3 route:

- an ambient normalized Laurent `Finsupp` is pushed to rational physical
  weights, with coincident restricted weights summed by `mapDomain`;
- the explicit fifteen left-handed Standard Model weights have fifth moment
  exactly `FifthMomentHypercharge.smFifthMoment`;
- arbitrary virtual gauge-singlet multiplicity at zero physical weight has
  vanishing fifth moment;
- an exact SM-only restriction with a nonzero integer generation count
  supplies `HasSMFifthMoment` and forces `(m,n)=(-2,3)`;
- every finite charged collection of actual finite-dimensional jointly
  continuous unitary `SU(6)` representations now exposes the common
  `VirtualAmbientLaurentModel` needed to instantiate that result.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB3.lean` permanently audits each stage.  The focused audit
completed with 3806 jobs and every newly audited declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`.  The full root build completed
with 3852 jobs.

This closes the exact fifth-moment source bridge in the jointly continuous
unitary scope, conditional only on the stated exact finite-weight restriction
equality.  It does not yet prove continuous unitarizability for every broader
continuous/smooth/algebraic representation, nor derive that exact equality
from an informal physical spectrum statement.  A1 and C1 retain their stated
source obligations, C3 remains auxiliary, D remains independent, and no final
no-go theorem is claimed.

---
