# Actual Common Light Quotients

## Statement

`NonabelianSMTarget.Matches` assigns five actual residual representations to
the fifteen oriented SM weights. At each weight the target character equals
the light-sector character minus the dual character of the opposite-weight
light sector. No condition is imposed at other weights. Finite dimensionality
is required at constituent extraction; `Matches` itself is just a character
identity and does not bundle that hypothesis.

`characters_compatible` derives target character equalities Q/up/electron
and down/lepton from the three actual ambient conjugations and invariant
symmetric mass. It does not assume that the conjugators preserve the radical.
No commutativity or finiteness of the residual group is used in this step.

For finite H, `common_ten_quotient` and `common_barFive_quotient` construct one
nonzero irreducible constituent for each of the two families and split
equivariant projections onto it from all corresponding light weight spaces.
They require finite-dimensional targets and nonzero Q/down targets separately;
their dimensions need not coincide. The two constituents need not coincide.

## Construction

- [Finite irreducible quotient](../../../Math/RepresentationTheory/Decomposition/FiniteIrreducibleQuotient.lean):
  select a nonzero block from the existing semisimple decomposition, and use
  mathlib's Maschke/lifting property for equivariant right inverses.
- [Light quotient](../../../Physics/FieldTheory/Mass/ResidualLightQuotient.lean):
  positivity uses the actual dual opposite-weight representation as remainder.
  The character/Hom dimension formula supplies surjections, then Maschke splits them.
- [SM source](../../../Physics/StandardModel/Spectrum/NonabelianLightSource.lean):
  derive compatibility before selecting common quotients. Entire light sectors
  are not required to be isomorphic. Extra paired matter remains allowed.

The splitting also supplies projections on contragredient fields by dualizing
the inclusion, not the projection. This is needed for the next tensor step.

## Boundaries

Verification: the three focused audit targets passed (3836 jobs, 11 new strict
checks). Full `lake build` passed (5601 jobs); layout passed (580 modules);
documentation passed (238 Markdown files, 1278 links, 32 fragments).
New modules have no warnings; existing dependency warnings were replayed.
`git diff --check` passed. The branch remains unmerged by user request.

At this checkpoint ordered coefficients and Abelian recovery were separate
obligations; both are closed in the [final results](results.md). These results do not
establish a nonzero Lorentz/Grassmann operator, an interaction coefficient,
decay amplitude, lifetime, or any stronger E6 global-form claim.
