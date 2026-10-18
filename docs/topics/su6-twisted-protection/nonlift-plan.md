# Nonliftable UV inner C2 action: bounded concrete test

The user authorized checking the remaining nonhomomorphic-lift route.
On the same `15 + bar6 + bar6` component basis and mass as the preceding
[C4 test](block-phase-plan.md), choose

```text
s = diag(i,i,i,-i,-i,-i) in SU(6), s² = -I
beta(t) = s t s^-1, a C2 action on UV SU(6)
E = (1 on 15, i on both bar6 copies)
U = rho(s) E
```

Keep the neutral-external adjoint VEV `diag(1,1,1,1,1,-5)`, standard
SM placement and existing unit mass pairings. Residual Lorentz action is
trivial. The endpoint is one finite candidate: check U²=1, covariance,
VEV/mass/radical compatibility, nonexistence of any homomorphic SU(6) lift
of beta, visibility of the removed-action defect and physical qque survival.

The nonlift claim concerns the UV automorphism, not beta restricted to K.
Every other lift of the nontrivial beta generator differs from s by the
SU(6) center. Enumerate all six central corrections using twelfth-root
exponents; prove the centralizer step explicitly in the result note.
Use exact standard-library scripts, no new dependency, no extension
classification or new Lean theorem. Run both candidate scripts and the
reused qque audit, links and diff checks; commit on the existing topic branch.
Reject this candidate as a prohibition mechanism if a nonzero qque term
survives. Do not infer a generated interaction or a universal no-go.
