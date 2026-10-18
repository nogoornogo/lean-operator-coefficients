# B3 compact physical-torus character source bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: B3 compact physical-torus character source bridge milestone
- Local-model role: none

### Audit result

`GUT/SU6/Characters/PhysicalTorusCharacterBridge.lean` now replaces the internal exact
finite-weight source premise by a function-level physical-character premise:

- canonical ambient exponents restrict to an integral four-dimensional
  physical weight lattice for every integral centralizer pair `(m,n)`;
- casting this restriction to rational weights agrees exactly with the B3
  fifth-moment model, including summed weight collisions;
- the explicit fifteen-weight SM target and arbitrary zero-weight singlet
  index are realized in the integral lattice;
- the physical compact four-torus is mapped to the actual determinant-one
  ambient diagonal torus, and every ambient Fourier monomial pulls back to
  its restricted physical monomial;
- multivariable Fourier independence makes the physical evaluator faithful;
- consequently, pointwise equality of the actual finite virtual restricted
  character with the explicit SM-plus-singlets target implies the exact
  `Finsupp` spectrum and forces `(m,n)=(-2,3)` for nonzero generations;
- the final result is instantiated directly for finite virtual collections of
  actual jointly continuous unitary `SU(6)` sources.

The focused B3 audit completed with 3807 jobs and every newly audited
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The full root build completed with 3853 jobs.

The remaining B3 scope issue is general continuous unitarization unless
physical admissibility is explicitly unitary.  The final physical model must
also supply the now-explicit compact-torus character equality from its
SM-only-spectrum hypothesis.  A1 and C1 remain separately conditional, C3 is
auxiliary, D is independent, and no final no-go theorem is claimed.

---
