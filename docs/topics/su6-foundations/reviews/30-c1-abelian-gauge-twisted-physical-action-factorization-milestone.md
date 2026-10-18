# C1 Abelian gauge-twisted physical-action factorization milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 Abelian gauge-twisted physical-action factorization milestone
- Local-model role: none

### Audit result

The finite-sector result was first strengthened: finite-dimensional unitarity,
not finiteness of the residual group, supplies semisimplicity.  Consequently
every supplied unitary action of an arbitrary Abelian group decomposes into a
finite independent family of full character eigenspaces, reconstructing the
original `SU(6)` representation and trace character.  The previously checked
finite-Abelian statements remain explicit specializations.

`GUT/SU6/Hypercharge/StandardCentralGauge.lean` now constructs the concrete continuous
homomorphism
`Circle -> SU(6), z |-> diag(z,z,z,z,z,z^-5)` and proves that every ambient
Laurent monomial restricts to `z^totalDegree`.

`GUT/SU6/ProtonStabilityNoGo/StandardBranch/FiniteResidualActionFactorization.lean` now checks the following
physical-source chain:

- a unitary residual action satisfying covariance through a homomorphic inner
  `SU(6)` gauge lift factors into that lift and a unitary action commuting with
  all of `SU(6)`;
- if the physical action and standard-central character are continuous, the
  external action and every selected sector character are continuous;
- for a residual circle, each selected character has a unique integer charge;
- on every vector of the exact integral-weight basis used by the B3 Laurent
  model, the original physical action has phase
  `offset(h) * eta(h)^totalDegree`;
- exact pure-SM source certificates therefore give trivial proton-operator
  characters for arbitrary Abelian, continuous Abelian, and finite Abelian
  residual groups by C1 followed by C2, without using C3.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditC1.lean` permanently audits these declarations.  All newly
audited results depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The focused audit completed with 3810 jobs and the full root
build with 3851 jobs.  `git diff --check` passed, and no Lean source contains
`sorry`, `admit`, or a declared `axiom`.

This remains a conditional physical-source bridge.  A universal theorem must
still derive the homomorphic gauge lift and its standard-central reduction
from every intended model, derive the exact charge-resolved low-energy
spectrum and nonzero gauge amplitudes, and close A1 and the full intended B3
scope.  C3 remains only an auxiliary continuous-`U(1)` anomaly cross-check;
D remains an independent representation-theoretic obstruction; no final
no-go theorem is claimed.

---
