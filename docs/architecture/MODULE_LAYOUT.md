# Source Layout

Sources are organized by subject and application, not by proposed upstream
destination. The three Lake libraries share the existing dependency pins:

```text
Math/
  LinearAlgebra/             bases, exterior algebra, quaternionic spectral theory
  RepresentationTheory/
    Characters/              characters, charge sectors, virtual representations
    Decomposition/           irreducibility, Schur, products and transport
    Multiplicity/            commutants, multiplicity models and centralizers
    Unitary/                 invariant inner products and continuous actions
  LieAlgebras/               root spaces, Geck/Serre comparisons, certificates
  LieGroups/
    Matrix/                  exponentials, normalizers, local logarithms
    SpecialUnitary/          SU(n) blocks, representations and topology
      RankFive/              rank-five weight permutation algebra
    Torus/                   circle homomorphisms and integer character lattices
    Symplectic/              compact group, quaternionic basis, torus conjugacy
    Spin/                    Clifford model, covering and SU(5) inclusion
    E6/Minuscule/             compact matrix candidate and its geometry
  Topology/                  coverings, paths, fundamental groups
  Audit/                     relocation identity helper
Physics/
  FieldTheory/
    Mass/                    invariant masses, radicals and character indices
    Yukawa/                  scalar-dependent and multilinear mass families
  StandardModel/
    Gauge/                   gauge tensor algebra and pairings
    Spectrum/                SM targets, charge profiles and chiral indices
    Operators/               supported signatures and charge selection rules
GUT/
  Common/
    StandardChain/           common ambient-group selection-rule consumers
    Chirality/               common self-dual-source obstruction
  SU5/                      embedding, branching and retained matter theorem
  SU6/                      scoped classification, hypercharge and two branches
    Adapters/                interfaces tied to concrete SU6 source models
    Yukawa/                  SU6-specific unitary scalar completion
  SUN/                      standard SU(N) chain and rank-seven benchmark
  Sp/                       symplectic character/mass and SM chirality consumers
  Spin10/                   branching, half-spin benchmark and selection rule
  E6/                       SU5 model comparison and positive-target application
```

Each subject keeps persistent checks in a nearby `Audit/` directory. A mixed
audit remains beside its application when it checks physical consequences as
well as mathematical constructions. Empty speculative folders are not created;
for example zero-mode results currently belong with the mass data they consume.

## Dependency Direction

- Math may depend on mathlib/TauCeti and other Math modules, not Physics or GUT.
- Physics may depend on Math and other Physics modules, not GUT.
- GUT assembles application statements from either lower layer.

Group-specific does not mean application-specific: compact symplectic matrices,
Spin coverings, SU(n) simple connectedness and the E6 compact candidate belong
to mathematics. Conversely, a file using an SU6 actual-spectrum interface or
an SU5 matter model remains an application adapter even if it proves some
generic-looking consequences. Placement does not assert unconditional global
group identification or physical realizability.

Generic unitary and continuous-action interfaces, virtual representations,
Schur lemmas, basis traces, tensor constructions and Haar averaging have been
extracted from mixed modules without changing declaration names or proof bodies.
The compact-product module is also split: its general theorem is in Math and
its SU2/SU3 classification application in `GUT/SU6/Adapters`.
Further API generalization is a separate topic, not an excuse for upward imports.

## Imports And Names

Model-specific selection-rule applications use `SelectionRules/`. The former
`ProtonStabilityNoGo/` directories were renamed without changing theorem names
or their hypotheses. The source map retains their original audit identities.

The original file relocation kept declaration names. The subsequent
[Math namespace migration](../topics/math-namespaces/README.md) changes
Math-owned `GUT.*` names to `Math.*`, including uses in Physics and GUT.
Shared Physics/GUT namespace extensions retain their own declaration ownership.
No legacy declaration aliases are provided; external callers must update them.
Import paths and historical module identities remain unchanged. For example:

```lean
import Math.RepresentationTheory.Characters.CharacterRestriction
#check Math.CharacterRestriction.virtualCharacter
```

The [old-to-new path map](../../tools/layout/source-map.json) records relocated
files. It is not a set of compatibility forwarding modules: old import paths
must be updated. Keeping duplicate wrappers would obscure the layer boundary.
`Math.lean` and `Physics.lean` aggregate their libraries; `GUT.lean` includes both
and every application/audit. `lake build` still checks the entire project.

## Verification And Discovery

```sh
node tools/layout/check-layout.mjs
node --test tools/layout/test-check-layout.mjs
lake build
node tools/docs/check-links.mjs
```

The [layout checker](../../tools/layout/README.md) checks source-level imports,
cycles, aggregate coverage and relocation identities. Existing import exclusions
are evaluated against their original module identities so a rename cannot bypass
them. Existing transitive axiom allowlists are unchanged.

Use [source search and Lean LSP](LEAN_TOOLING.md) for focused inspection, and
[doc-gen4](DOCUMENTATION.md) for generated API browsing. After moves, old generated
HTML and orphaned compiled artifacts are stale; they are not source authority.

## Proof Navigation

- [Current proof guide](../proof/README.md), [interfaces](../proof/INTERFACES.md)
  and [topic outcome guide](../topics/_history/README.md).
- [Representation centralizers](../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md).
- [Shared selection rules](../proof/current/applications/Physics/SHARED_SELECTION_RULES.md).
- [Standard SU(N)](../proof/current/applications/GUT/interfaces/standard-su-n.md),
  [Spin(10)](../proof/current/applications/GUT/SPIN_STANDARD_CHAIN.md),
  [symplectic chirality](../proof/current/applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md).
- [E6 positive target](../proof/current/applications/GUT/E6_POSITIVE_TARGET.md) and
  [explicit literature boundary](../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).

E6 maximal-torus fundamental-group surjectivity remains an explicit input.
Moving its conditional consumer into Math does not close that assumption.

Upstream suitability is judged [file by file](UPSTREAMING.md), including transitive
dependencies and licensing, only when a concrete contribution is proposed.
See [the migration record](../topics/math-physics-gut-layout/README.md).
