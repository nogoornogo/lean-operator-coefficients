# A Nonliftable UV Inner C2 Action With Surviving qque

## Concrete Action

The [bounded plan](nonlift-plan.md) tests the actual 27-component
`15 + bar6 + bar6` basis of the previous [C4 candidate](block-phase-result.md).
Choose

```text
s = diag(i,i,i,-i,-i,-i) in SU(6)
beta(h)(t) = s t s^-1, h the generator of C2
E = (1 on 15, i on both bar6 copies)
U(h) = rho(s) E
```

Here `s²=-I`, so beta has order two. It is nontrivial on a color/weak
off-block matrix unit. The center `-I` acts as +1 on the exterior-square 15
and -1 on each dual six. Thus `rho(s)² E² = identity`: U is a genuine,
nontrivial C2 action on matter, although E itself is not a C2 representation.
E commutes with every UV gauge action because it is scalar on each summand;
therefore U has the prescribed inner covariance on the full UV group.
The script checks that identity on all matrix units of the complexified Lie
algebra; this is not a new formal full-group covariance certificate.

## Why No Homomorphic SU(6) Lift Exists

If another t implements the same conjugation on all SU(6), `s^-1 t`
commutes with every SU(6) matrix. Such a matrix is scalar: commuting with
diagonal sign matrices with two minus signs forces every off-diagonal entry
to vanish, and commuting with determinant-one signed coordinate exchanges
forces all diagonal entries to agree. Both families lie in SU(6).
The script also checks the corresponding 36-variable linear system has
rank 35 over the rationals, with the identity matrix in its kernel.

Consequently every t is `z^k s`, where `z=exp(2 pi i/6) I` and k=0,...,5.
A homomorphism from C2 would require `t²=I`, but

```text
(z^k s)² = z^(2k+3) I != I.
```

The exponent `2k+3` is odd, and cannot be divisible by six. In twelfth-root
units, the six squared phases are `[6,10,2,6,10,2]`, none zero.
This excludes every homomorphic lift of this beta to SU(6), not merely the
chosen section s. It does not exclude lifts into other groups.

For the normalized section, `d(h,h)=(s s)^-1=-I`. The removed map is E,
and `E²=rho(d(h,h))`. The defect is visible on both dual-six summands and
on the five light first-copy components d^c/L. Hence the removed UV action
fails the C2 field group law, exactly as the existing
[defect criterion](defect-result.md) predicts on the UV carrier.

## Vacuum, Mass And Light Coefficients

Retain the neutral-external adjoint vacuum `diag(1,1,1,1,1,-5)` and the six
unit symmetric Dirac pairings defined in the [preceding plan](block-phase-plan.md).
The vacuum is fixed. The same mass matrix has rank 12 and the same exact
15-dimensional light radical; every massive pair has total U phase +1.
Standard gauge-algebra invariance and hypercharges are unchanged and checked
by rerunning the preceding audit. A UV scalar origin for this mass and quantum
exactness of C2 are still unverified.

| Light field (all left handed) | U phase |
| --- | --- |
| Q | +1 |
| u^c, e^c | -1 |
| d^c | +1 |
| L | -1 |

The dual fields u_R and e_R are also odd. Thus `Q Q u_R e_R` is even.
With residual action trivial on Lorentz indices, the reused one-generation
Lorentz/Grassmann qque contraction retains all 24 nonzero monomials and its
selected coefficient 2. **This candidate does not prohibit qque.** An allowed
coefficient is not a generated interaction or a decay-rate calculation.

There is an essential scope distinction: s is scalar on the standard color
and weak blocks, so beta restricted to the chosen SM group K is identity.
That restricted action has the identity homomorphic lift, and U commutes
with K. Nonliftability holds on UV SU(6), and does not make the low-energy
K action nonliftable. Nor does the single supplied adjoint VEV claim complete
breaking to precisely K. This result does not exclude other finite actions,
light placements or non-split protection mechanisms.

## Verification

The [audit](../../../tools/su6-twisted-protection/audit_nonlift.py) uses exact
integer/fraction/root-exponent arithmetic. Its six tests cover the complete
lift list, scalar centralizer, finite orders, covariance, visible defect,
vacuum/mass/radical compatibility and all nonzero physical qque terms.
Negative controls include a liftable order-two generator and a changed
electron sign. These checks are not Lean certificates.

- `python3 tools/su6-twisted-protection/audit_nonlift.py`: six tests passed.
- `python3 tools/su6-twisted-protection/audit_block_phase.py`: six tests passed.
- `python3 tools/qque/audit_one_generation.py`: four tests passed.
- Local links and `git diff --check`: passed.
- No Lean sources changed; no Lean build or axiom audit was rerun.

This bounded candidate test is complete; the parent topic remains open
without a protecting model. Master integration is not authorized.
