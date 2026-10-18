# primitive physical circles and the concrete cocharacter tangent bridge

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: primitive physical circles and the concrete cocharacter tangent bridge
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- a two-torus power circle with exponent pair `(m,n)` is injective exactly
  when `gcd(m,n)=1`; this is transported to the actual physical centralizer;
- along the standard real parameterization `Circle.exp`, the complex
  coefficient `z |-> z^n` has derivative `i*n` at the identity;
- differentiating the actual centralizer action on every defining-space vector
  gives the checked anti-Hermitian generator with real `Y5/X` coordinates
  `((n-m)/5,(3m+2n)/5)`;
- the standard-basis matrix curve used in this calculation is proved equal to
  the underlying matrix of the actual `SU(6)` centralizer element;
- the matrix curve itself has the expected derivative, and every arbitrary
  continuous physical-centralizer cocharacter has a unique integer pair
  together with this derivative statement.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditCircleHomLattice.lean` now audits the primitive-pair theorem and
the reusable scalar derivative.  `GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` audits the transported
primitive criterion, actual matrix equality, matrix derivative, and the final
arbitrary-cocharacter theorem.  Every new declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

The full build completed successfully with 3813 jobs.  The Lean source tree
contains no `sorry`, `admit`, or declared `axiom`.  This closes the concrete
matrix-level B1 bridge from the topological two-torus through its integer
cocharacter lattice to the anti-Hermitian `Y5/X` generators.  A separate
smooth-manifold tangent-bundle presentation remains optional packaging rather
than a dependency of this result.

---
