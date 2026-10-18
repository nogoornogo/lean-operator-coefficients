# Hermitian Action Recalculation Plan

## Frozen scope

Continue the existing unmerged branch, with one Majorana N and the selected
u,d,s channel. Use an actual complex-conjugating star-ring interface for H.c.;
barred vertices are stars of the original vertices, not independent inputs.
Count the scalar quadratic term once. Prove Hermiticity and exact scalar
elimination in Lean, including both cross channels. Recalculate the full
Grassmann action through external degree six with exact rational arithmetic,
including all four heavy fermion components and their left stationary
equations. Check the degree-five stationary residual, H.c., the holomorphic
projection and the earlier selected coefficient.

The computation is a bounded diagnostic, not a Lean premise. A generic
star-ring interface does not construct a star instance on the project's
physical exterior carrier. Do not claim a fully formalized heavy-field
stationarity theorem from this diagnostic. Stop at verified scalar elimination
and reproducible degree-six matching, or a precise obstruction. No kinetic
propagators, loops, additional flavors/N copies, rates, dependency changes,
master merge or remote push. Maintain the source-adoption boundary.

## Existing inputs

- [Earlier completion](external-leg-results.md) and its explicit missing premises.
- [Literature dictionary](literature-evaluation-results.md).
- Math.AlgebraValuedQuadraticElimination for exact paired elimination.
- Physics.FieldTheory.Mass.ChiralActionConvention for the existing supplied
  complex star-algebra interface.
- mathlib CliffordAlgebra/Star.lean: its star fixes scalar coefficients,
  so it is not used as the complex Hermitian conjugation here.

## Verification

Focused Lean build, persistent strict transitive audit, full lake build,
exact finite diagnostic, layout, documentation links and diff checks.
