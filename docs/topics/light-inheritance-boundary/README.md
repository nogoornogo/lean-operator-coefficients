# Light-Field Inheritance Boundary

- ID: light-inheritance-boundary
- Status: completed
- Checkpoint detail: completed (counterexample endpoint; integration recorded by Git).
- Result type: bounded feasibility check and algebraic counterexample.
- Working branch: `proof/light-inheritance-boundary`.
- Integration target: `master`.

## Frozen Endpoint

Check whether the existing mediator inheritance conditions also transport
actual light fields and their residual symmetry to full-species completeness.
Route one inspects the existing exchange and equivariant mass transport APIs.
Route two checks whether an equivariant retained matter inclusion and agreement
of the restricted fermion mass suffice to preserve the radical. Stop on a
counterexample; do not add a new spectrum hypothesis or a certificate layer.

The mediator mass-squared operator and the fermion symmetric mass are distinct
inputs. Keep their roles explicit. No new GUT, amplitude, vacuum, dependency,
axiom or physical-scope claim is included.

## Interfaces

- [Mediator inheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)
- [Qque inheritance](../../../Physics/StandardModel/Operators/QqueMediatorInheritance.lean)
- [Equivariant mass transport](../../../Physics/FieldTheory/Mass/EquivariantWeylMassTransport.lean)
- [Dirac mass convention](../../../Physics/FieldTheory/Mass/DiracWeylConvention.lean)
- [Concrete light connection](../light-matching-coherence/joint-species.md)

## Results

The existing mediator criteria compare exchanges on the SAME external field
spaces and representations. `QqueMediatorInheritance.sector_eq` preserves
the generated sector for those supplied representations. Neither API takes
a fermion mass or constructs new light species from a new radical.

The [checked counterexample](../../../Physics/FieldTheory/Mass/LightInheritanceBoundary.lean)
uses any representation rho of any group G, hence also G = SM x H.
Start with zero fermion mass on V. Include V equivariantly and injectively
into V x V.dual by x -> (x,0). The invariant symmetric mass

    B((x,phi),(y,psi)) = psi(x) + phi(y)

restricts to the original zero mass on V x V, but its full radical is zero.
`light_not_preserved` proves that every nonzero old light vector leaves the
new radical. `pairedMass` uses the existing `ofDirac` construction with the
identity intertwiner, so full G-invariance is proved, not assumed separately.
No finite-dimensionality or topological condition is needed.

This failure occurs before any issue of reconstructing a qque coefficient.
Mediator support/mass equations do not involve this fermion mass and can be
left unchanged (including the identity inheritance case). They therefore
cannot, by themselves, force an inclusion of the old actual radical.
The counterexample does not construct a complete larger GUT with prescribed
UV currents, a vacuum or the original positive chiral index. Adding V.dual
changes that index. It does NOT refute the existing index/spectrum-conditioned
selection-rule theorems, nor settle transfer under all their extra hypotheses.
It refutes automatic light-field inheritance from the mediator conditions,
even supplemented by equivariant inclusion and restricted-mass agreement.

## Conditional Route And Stopping Decision

`EquivariantWeylMassTransport.radicalEquiv` already transports the actual
radical and its full residual action when an equivariant equivalence of
matter and a pullback relation for the fermion mass are supplied. This is a
valid existing route for compatible changes of presentation. An inclusion
into larger matter is not such an equivalence.

For an inclusion i, the missing condition is control against ALL ambient
fields: B'(i x,y)=0 for every ambient y whenever x is old-light. Knowing
only B'(i x,i z)=B(x,z) leaves cross-pairings with added matter uncontrolled.
A derived identity B'(i x,y)=B(x,p y) would suffice for radical inclusion;
it is a fermion-mass condition independent of the mediator-mass conditions.
For a full canonical-species identification, exhaustiveness must also be
checked. For nonzero exchange alone, one may instead use a retained probe
on the target species together with full target invariance. These obligations
are not proved by the counterexample or silently added as premises here.

Stop at the counterexample as requested. No certificate abstraction is started.
Further work needs a choice of a spectrum/mass class with controlled cross
pairings, or a restricted compatible-equivalence endpoint. A theorem for
all larger GUTs does not follow from the existing mediator conditions alone.

## Verification

- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditLightInheritanceBoundary`:
  passed; six strict transitive axiom checks, only `propext`, `Classical.choice`,
  `Quot.sound`. An initial `Submodule.mem_bot` elaboration error was corrected.
- Full `lake build`: passed, 5835 jobs.
- `node tools/layout/check-layout.mjs`: passed, 784 modules.
- `node tools/docs/check-links.mjs`: passed, 296 Markdown files, 1783 local
  links and 33 fragments. `git diff --check`: passed.
- Lean LSP unavailable; used source inspection and builds. New source has no
  warnings; dependencies replay existing warnings. No pin or audit changes.
- Existing qque exact regression scripts were not rerun: no exchange,
  contraction, statistics or normalization definitions changed.
- Commit and no-ff merge to master after verification; retain the branch and
  repeat build/consistency checks on the merged state. No push.
