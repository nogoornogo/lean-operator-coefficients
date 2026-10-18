# Exact PS Component Controls

Run `python3 tools/ps-bnv-coefficient-bridge/audit_ps.py` from the repository root.
Only the Python standard library is used; rational and Gaussian-rational
arithmetic is exact. The eight checks cover the epsilon factors, the QQ
covariant half, full Grassmann RR/LR nonzero polynomials, the mass-chart residual,
barred complex projection, scalar zero/cancellation/invalid-inverse controls,
independent chiral probes and dimension/charge bookkeeping.

These are supplementary controls, not Lean proof premises or a full
literature/sector correspondence. No rates, floating-point simulation, loops,
RGE or hadronic inputs are computed. The formal certificate and its source
normalization stop are in the [topic result](../../docs/topics/ps-bnv-coefficient-bridge/result.md).

The follow-up adds a rational canonical-norm control for d/M=3/4 and
3i/4, checking the normalized mass kernel, conjugate projection and invertible
coordinate transport. These two samples supplement, and do not establish,
the general Lean normalization theorem.

The connection phase adds exact Grassmann mass-action checks (including the
Majorana half), and finite common-factor compatibility controls. Real.sqrt(2)
is handled by Lean; the script does not approximate it or certify all field
redefinitions.

The action translation adds an exact Gaussian-rational Grassmann star test.
Dagger reverses generator order and conjugates coefficients. It checks the
barred/chiral Yukawa conversion and the kinetic matrix identity modulo a
formal divergence. No spacetime evolution or boundary-value calculation is run.

Mechanism-completion controls check an exact two-copy mass kernel with
non-diagonal heavy mixing over 729 rational candidate vectors, plus a nonzero
ambient wedge that vanishes on the light graph. A squared-norm control tests
the fixed-convention discrepancy without evaluating square roots numerically.
