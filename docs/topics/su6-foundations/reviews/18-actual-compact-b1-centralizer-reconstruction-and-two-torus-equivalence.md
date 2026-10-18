# actual compact B1 centralizer reconstruction and two-torus equivalence

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: actual compact B1 centralizer reconstruction and two-torus equivalence
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- the coefficient group `{(c,w,s) in Circle^3 | c^3*w^2*s=1}` is continuously
  group-equivalent to `Circle x Circle` by explicit inverse maps;
- orthogonal projection onto a unitary invariant subspace is an intertwiner,
  so Schur's lemma makes actual irreducible constituent ranges of dimensions
  `3`, `2`, and `1` pairwise orthogonal;
- every actual `SU(6)` centralizer element has unique unit-circle block
  coefficients satisfying the special-unitary determinant equation, and this
  coefficient homomorphism is injective;
- every determinant-one coefficient triple acts unitarily on the three actual
  orthogonal constituents; its standard-basis matrix is in `SU(6)` and
  centralizes the embedded semisimple image;
- reconstruction followed by coefficient extraction is the identity, making
  the coefficient homomorphism surjective and giving an abstract group
  equivalence from the physical centralizer to `Circle x Circle`.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditB1.lean` permanently audits the new determinant, orthogonality,
unitarity, injectivity, surjectivity, and group-equivalence declarations.  All
audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The A1 and D2/D3 audits also pass.  The full build completed
successfully with 3789 jobs, and the Lean source tree contains no `sorry`,
`admit`, or declared `axiom`.

The remaining B1 refinement is to prove continuity of the actual-centralizer
group equivalence and to identify its anti-Hermitian tangent real form and
integral lattice with the checked `Y5/X` parameterization.

---
