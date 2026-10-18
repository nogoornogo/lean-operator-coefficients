# circle cocharacter lattice of the actual B1 centralizer

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: circle cocharacter lattice of the actual B1 centralizer
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- every continuous circle endomorphism lifts through `Circle.exp` to a unique
  continuous real-valued map fixing zero;
- uniqueness of covering-space lifts makes that lift additive, continuity
  makes it real-linear, and the `2*pi` period forces its slope to be an
  integer;
- consequently every continuous circle endomorphism is a unique power map
  `z |-> z^n`, and every continuous homomorphism into `Circle x Circle` has a
  unique exponent pair in `Integer x Integer`;
- transport across the checked actual-centralizer `ContinuousMulEquiv`
  classifies every physical-centralizer circle homomorphism by such a unique
  pair `(m,n)`;
- actual coefficient extraction gives color, weak, and singlet exponents
  `(m,n,-(3m+2n))` exactly;
- the algebraic conversion to the checked real `Y5/X` coordinates is
  `((n-m)/5,(3m+2n)/5)`, is injective, and recovers all three block slopes.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditCircleHomLattice.lean` permanently audits the reusable
covering-space classification, while `GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` audits its
physical transport, determinant-forced exponent, and `Y5/X` coordinate map.
All new audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The full build completed successfully with 3810 jobs, and the
Lean source tree contains no `sorry`, `admit`, or declared `axiom`.

The remaining interface is differential: show that the tangent of each
checked integer cocharacter is the corresponding checked anti-Hermitian
`Y5/X` element.  The lattice classification itself is now complete.

---
