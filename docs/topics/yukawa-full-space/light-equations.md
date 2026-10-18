# Actual Light-Space Equations

Status: bounded endpoint completed and verified. Branch `proof/yukawa-full-space`, checkpoint `checkpoint 01`,
integration target `master`; parent endpoint remains open.

## Frozen Endpoint

For the unchanged actual SU(6) matter, scalar and specified vacuum, derive
necessary and sufficient equations for membership in the full radical of
the five-parameter generated mass. Use the proved exhaustive vacuum image
to cover arbitrary allowed Yukawas, not only specially chosen couplings.
No generic nonzero assumptions, potential minimization or numerical premises.

Write z for the contracted exterior coordinate, f and g for the two dual
coordinates. For each i < 5, the expected equations are
`a*f_i + b*g_i = 0`, `a*z_i = 0`, `b*z_i = 0`; the remaining equations are
`u*f_5 + v*g_5 = 0` and `v*f_5 + w*g_5 = 0`.
The exterior components with both indices below 5 are unconstrained.

Prove these equations from evaluation on the actual basis, then package
the full radical as a kernel of explicit linear constraints. A dimension
or representation decomposition requires a separately proved coordinate
equivalence, not just agreement with the external matrix pattern.
This milestone stops at the exact full-radical criterion and its kernel
equivalence; full 22-dimensional coupling classification remains separate.

## Verification

- `lake build GUT.SU6.Audit.AuditYukawaLightEquations`: passed, 4254 jobs;
  20 strict transitive checks, allowing only propext, Classical.choice and
  Quot.sound. No new-source warnings; existing dependency warnings replayed.
- Full `lake build`: passed, 5863 jobs.
- `python3 -m unittest discover -s tools/yukawa -p 'test_*.py'`: 8 passed,
  1.1 seconds. These are supporting controls, not premises of Lean proofs.
- `node tools/layout/check-layout.mjs`: passed, 812 modules.
- `node tools/docs/check-links.mjs`: 306 Markdown files, 1861 links,
  33 fragments, zero errors. `git diff --check`: passed.
- Lean LSP unavailable. No web sources consulted for this milestone.
  No pins, resource limits, axioms or audit exceptions changed. Qque scripts
  not rerun because their covered definitions are unchanged.

## Result And Boundary

[LightEquations](../../../GUT/SU6/Yukawa/LightEquations.lean) proves:

- `row_exterior`, `row_first`, `row_second`: actual mass evaluations on all
  27 basis directions, including the ten unconstrained exterior directions.
- `radical_iff`: the full light space is characterized by the displayed
  equations, with no genericity or nonzero hypotheses.
- `radical_eq_kernel`, `radicalKernelEquiv`: equality with the kernel of an
  explicit linear map on actual UV fields, not an assumed normal form.
- `all_yukawas`: every allowed Y has coefficients realizing this mass and
  this same necessary-and-sufficient radical criterion.
- `untouched_light`: every exterior basis direction with both indices below
  5 is light for all coefficients.
- `pureSinglet_light_iff` and `nonzero_couplings_light_singlet`: exact 2-by-2
  singlet equations and a nonzero actual light singlet at a=b=u=v=w=1.
  This confirms that nonzero couplings alone do not determine the spectrum.

[Persistent audit](../../../GUT/SU6/Audit/AuditYukawaLightEquations.lean).
The first monolithic criterion proof hit the elaborator heartbeat limit;
abstracting the bilinear form in `vanishes_iff` resolved it. Constraints are
assembled from linear coordinate maps instead of repeatedly simplifying
their concrete representation implementations. No limits or pins changed.

This milestone did not prove the dimension list or residual multiplicities.
The subsequent [spectrum transport](spectrum-transport.md) supplies the
bijective coordinates and kernel transport to `SmallSymmetricRank`, plus
an equivariant singlet splitting. Non-singlet decomposition and the full
coupling-space classification remain separate open obligations.
