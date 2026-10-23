# Source API Migration

The migration marker `source-api-v1` identifies this compatibility transition;
it is not a Lean, dependency or package release number. Legacy imports and names
remain available during the transition and warn with their replacements.
Their eventual removal belongs to a future breaking release.

## Protected Surface

All existing import paths affected by subdivision remain forwarding modules.
Math declarations retain their current names. Physics declarations acquire the
`Physics` root; application declarations defined under GUT remain GUT-owned.
The declaration registry records defining-module ownership before renaming.
Source-declared public Physics names and their public constructors, projections,
recursors and instances receive legacy aliases. Private/compiler implementation
names absent from the registry are outside this surface. Existing nonderivative
inputs remain usable.

Instances and automation attributes belong to the canonical declarations.
Legacy aliases do not register second copies. Old-client checks exercise
construction, projection, dot notation, coercions, instance search and simp.

The [original frozen registry](layout-plan.json) and its
[shared-restriction addendum](registry-addendum.json) cover 12,989 legacy names, including
generated public constructors/projections and elimination principles. Together they
record 1,676 canonical moves (781 Math, 895 shared Physics implementations). Existing Math subject
namespaces remain stable. Registered public equation lemmas are also retained;
private names and unregistered compiler helpers are outside the protected API.
Generated equation lemmas for imported types retain their upstream namespaces.

Aliases retain old type heads in their argument types, so old field notation
continues to work. Constructor aliases also support old patterns. Ordinary
type abbreviations alone do not establish these properties; the persistent
[controls](../../../Physics/Compatibility/Audit/Structures.lean) check them.
Use canonical names for reflection on declaration kinds or defining modules:
legacy types are reducible aliases, and their kernel declaration category and
owning module differ from the canonical structure. Compiled clients must rebuild.

The generic unitary-restriction implementation moves from
`GUT.SU6.Representations.UnitaryVirtualRestriction` to
`Physics.FieldTheory.Mass.Spectrum.UnitaryVirtualRestriction`. Its nine old
names remain in the deprecated GUT import, with the old type heads needed for
method notation. [Old-route controls](../../../GUT/Compatibility/Audit/LegacyRestriction.lean)
check repeated restriction calls and the finite-sum compatibility theorem.
The declaration-free `GUT.SU5.Branching.TorusCharacter` import carrier also
retains its transitive legacy Physics names. Canonical code imports
`GUT.SU5.Embeddings.MaximalTorus` and
`Physics.StandardModel.Spectrum.Representations.TorusCharacter` directly.

## Mass Spectrum Pilot

| Previous import | Canonical import |
| --- | --- |
| `Physics.FieldTheory.Mass.AbelianMassSpectrum` | `Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum` |

Replace `GUT.AbelianMassSpectrum` with `Physics.AbelianMassSpectrum`.
The ten public declarations have unchanged statements and proof bodies.
The old module imports the canonical implementation and provides deprecated
aliases; it contains no duplicate proofs or instance registrations.

```lean
import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum
#check Physics.AbelianMassSpectrum.exists_zeroMode_of_pos
```

The previous import and declaration name continue to compile, with migration
warnings. Historical imports retired before this transition are not restored.
