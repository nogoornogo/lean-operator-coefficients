# C1 affine Abelian physical-source bridge milestone

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: C1 affine Abelian physical-source bridge milestone
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- a residual Abelian charge on one ultraviolet `SU(6)` source is represented
  as an independent source offset plus a common homomorphic image of the
  central `U(5)` degree;
- affine charge resolution commutes with the full standard-branch `S_5`
  action, and non-injective push-forward sums charge collisions;
- finite virtual collections of supplied Laurent-modeled sources retain this
  chargewise Weyl invariance;
- every finite collection of actual finite-dimensional jointly continuous
  unitary `SU(6)` sources receives such a modeled charge-resolved character;
- exact pure-SM profiles imply both proton functionals vanish in any additive
  Abelian charge-label group, including finite Abelian groups and `ZMod N`;
- nonempty family-dependent `10` and anti-fundamental profiles yield occupied
  neutral proton sectors with the same finite-group specializations.

`GUT/SU6/ProtonStabilityNoGo/Audit/AuditC1.lean` permanently audits the affine projection, actual-source
construction, Weyl invariance, and anomaly-independent C1-to-C2 conclusions.
Every newly audited declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.  The focused C1 audit completed with
3807 jobs and the full root build with 3848 jobs.  `git diff --check` passed,
and the Lean source tree contains no `sorry`, `admit`, or declared `axiom`.

This is a checked source certificate, not yet a universal physical-source
theorem.  It remains to prove that every intended ordinary Abelian residual
action decomposes into character sectors and supplies the affine offsets, and
to derive the exact low-energy profile and nonzero-amplitude hypotheses.
Here a finite residual symmetry group and its additive character-label group
must be kept distinct.  C3 remains only a continuous-`U(1)` cross-check, D is
independent, and no final no-go theorem is claimed.

---
