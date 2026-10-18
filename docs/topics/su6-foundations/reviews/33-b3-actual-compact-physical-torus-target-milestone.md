# B3 actual compact-physical-torus target milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B3 actual compact-physical-torus target milestone
- Local-model role: none

### Audit result

`GUT/SU6/Branching/PhysicalSMTorusTarget.lean` now realizes both sides of the B3
function-level source premise representation-theoretically:

- every integral physical weight defines an actual one-dimensional
  representation of the multiplicative compact four-torus, with trace
  character equal to its Fourier monomial;
- every finite integral `Finsupp` character is realized as a finite virtual
  sum of those representations;
- the exact SM-plus-singlets `Finsupp` is therefore an actual finite virtual
  target, including arbitrary net gauge-singlet index;
- the physical four-torus maps homomorphically into the actual
  determinant-one diagonal `SU(6)` torus for every `(m,n)`;
- the trace character of an actual finite virtual `SU(6)` source restricted
  along this map agrees with its ambient restricted character;
- character equivalence between that restriction and the actual target
  supplies the already checked faithful-Fourier premise and forces
  `(m,n)=(-2,3)` for nonzero generations;
- the result is instantiated directly for finite virtual jointly continuous
  unitary sources.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB3.lean` permanently audits the construction, restriction, and
final character-equivalence theorem.  The focused audit completed with 3809
jobs and the full root build with 3854 jobs.  Every newly audited declaration
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

This removes the last purely polynomial object from the B3 target side.  It
does not yet derive the target character equivalence from a complete physical
SM-only spectrum interface, nor prove continuous unitarizability beyond the
explicit jointly continuous unitary scope.  A1 and C1 retain their separate
source obligations, C3 remains auxiliary, D remains independent, and no final
no-go theorem is claimed.

---
