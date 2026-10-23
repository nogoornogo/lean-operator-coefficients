# Compatible Source Layout And Namespace Refactoring

- ID: `source-api-compatibility`
- Status: completed; integrated into master
- Result type: compatible source refactoring with deprecated legacy routes
- Working branch: `refactor/source-api-compatibility`
- Integration target: `master`
- Branch base: `master`, independently of the unmerged `docs/input-interface-flow` branch
- Authorization: user-directed new branch; retain public-interface stubs and announce eventual removal

## Endpoint And Compatibility Policy

Organize crowded source directories by subject and align canonical namespace
ownership with Math, Physics and GUT. Preserve the designated public interfaces
through old import modules and old-name aliases/stubs during the transition.
The published nonderivative interfaces are part of that protected surface.
Do not require every subject namespace to equal its full file path.

Create an explicit old/new public API registry before implementation. Include
the types, constructors, projections, coercions, notation and instances needed
to use those interfaces, not only the named entry-point functions. Protection
is registry-based; it is not a promise that every internal proof name remains
stable. Resolve uncertain public/internal classifications before changing them.

Use `deprecated_module` on a legacy import facade and `@[deprecated ...]` on
legacy declaration aliases once working replacements exist. Replacement paths
and names must appear in the warning. Use the library migration marker `source-api-v1` for these shims. No removal
release or date is assigned by this topic.

README announces that the shims are transitional and will be removed in a
future breaking release after migration guidance is published. This topic
does not remove the protected shims. An intentional later removal requires
its own release/scope decision. Retained facade files may leave the old
directories crowded even after implementation bodies move into subdirectories.

## Frozen Boundaries

- Preserve mathematical statements, hypotheses, dependency pins, proof limits,
  strict axiom allowlists and the explicit E6 literature boundary.
- Preserve Math → Math and Physics → Math/Physics import direction. A legacy
  `GUT.*` alias in a designated compatibility module is an explicit compatibility
  exception to naming alignment, not permission to import GUT applications.
- Resolve shared Physics/GUT namespaces by defining-module ownership. Do not
  globally replace `GUT` or move application-owned declarations into Physics.
- Keep canonical instance and automation registrations unique. Aliasing a
  structure or theorem does not by itself establish constructor, dot-notation,
  coercion, typeclass or simplifier compatibility.
- Do not restore retired historical import routes automatically. Earlier layout
  and Math-namespace migrations did not keep their old paths/names; this migration
  explicitly retains the currently designated public surface instead.
- Source compatibility requires old-client compilation checks. It does not
  promise reuse of compiled `.olean` artifacts or compatibility with unknown
  external uses outside the registry.

## Staged Plan And Acceptance

1. **Freeze the protected surface.** Inventory documented entry points and their
   public type closure; record defining modules, old/new names, old/new import
   routes, attributes, instances and consumer tests. Rebuild this branch before
   freezing elaborated metadata; caches from another branch or a partial rebuild
   are not an ownership baseline. Compare the local publication
   tag and current master, while distinguishing that tag from externally verified
   publication state. Incorporate the separate input-flow examples only after
   their source branch is explicitly integrated.
2. **Pilot one family.** Start with `AbelianMassSpectrum`, whose current namespace
   is `GUT.AbelianMassSpectrum`. Freeze its canonical replacement name and file
   map, then add protected old-route/name shims and deprecation warnings. Check
   old and new consumers, type/evaluation preservation and its existing strict
   audit before extending the method to structures and shared namespace families.
3. **Refactor coherent families.** Subdivide representation-theory coefficient,
   selection and jet-coordinate families, SM operator families and field-theory
   jet families in separate verified batches. Keep file subdivision and namespace
   changes separately reviewable. Treat generated certificate chunks separately
   from conceptual source organization; preserve their resource boundaries.
4. **Update all consumers and audits.** Migrate repository code to canonical
   paths/names. Update aggregate imports, source-reading tools, documentation,
   namespace-based audit inventories and historical module-origin maps together.
   No inventory may silently lose checked declarations after a rename.
5. **Verify and settle.** Run focused builds, unchanged strict transitive axiom
   audits, old/new API consumers, serialized full `lake build`, layout checks,
   relevant tool regressions, local links and whitespace checks. Review the
   complete mapping and assumptions, then commit coherent milestones. Master
   integration remains a separate user instruction.

Use the existing two-thread convention, default proof options, a 16 GiB
address-space cap and a 540-second timeout per Lean/build command. Stop a batch
for a scope decision if it requires changing a theorem premise, weakening an
audit, relaxing a resource guard, or removing a protected interface. Do not
silently turn a failed compatibility check into an allowed breaking change.

## Result

Canonical implementations are split by subject, with shared Physics declarations
under `Physics.*` and model applications under `GUT.*`. Math subject namespaces
remain stable. The [frozen registry](layout-plan.json) and bounded
[addendum](registry-addendum.json) record 1,676 canonical moves and 12,989
protected old names. The 1,677 deprecated import routes include the moved
modules and one retained import-only GUT carrier. At that acceptance the source
graph contained 4,226 modules; old forwarding modules intentionally remain in legacy folders.

Old aliases retain the argument-type heads needed for field notation and the
constructor attributes needed for patterns. Instances and automation rules
remain registered only at their canonical declarations. Persistent consumers
cover records, projections, polymorphism, coercions, typeclass search, simp,
patterns, eliminators, executable data and the published nonderivative inputs.
Each protected alias has an individual type/value and strict transitive axiom
check. The migration marker is `source-api-v1`, independently of Lean and package
release numbers.

The generic unitary-restriction implementation moves from its historical GUT
location to shared Physics; its nine old names and old import remain available.
The declaration-free SU(5) torus import carrier also retains its transitive
legacy Physics names. Canonical consumers import its two defining modules
directly. These exceptions are explicit in the registry addendum.

The [verification record](verification.md) describes the complete acceptance
checks and two bounded build repairs: a six-quark identity now follows from an
existing independent coordinate identity, and eight finite-certificate modules
use synchronous elaboration. Mathematical statements, hypotheses, proof limits,
dependency pins and strict axiom allowlists remain unchanged. Exact source replay
and elaborated symbol-reference comparison distinguish these recorded changes
from mechanical relocation and renaming.

See the [migration guide](migration-guide.md) for protected routes, replacements
and the limits of source compatibility. Legacy stubs remain until a future
breaking-release decision; they are not removed by this topic.

The preceding documentation topic remains on `docs/input-interface-flow` and
has not been merged or included as an incidental dependency of this branch.
The user subsequently authorized the complete recorded branch chain through
master. [Master integration](master-integration.md) records the merged-state
checks, README review and local branch cleanup.

## Resource Follow-Up

The user-directed [fresh-compilation and proof-memory audit](../proof-memory-audit/README.md)
is complete and integrated through its recorded parent. The later
[structural cubature](../higgs-cubature-structure/README.md),
[upgrade guide](../publish-v1-upgrade/README.md) and model-input children are
also included in the authorized master integration. Their own hypotheses and
measurement checkpoints remain separate from this compatibility endpoint.

## References

- [Source layout and historical namespace policy](../../architecture/MODULE_LAYOUT.md).
- [Existing Math namespace migration](../math-namespaces/README.md).
- [Existing source relocation](../math-physics-gut-layout/README.md).
- [Input and implementation map](../../proof/INTERFACES.md).
- [Build conventions](../../architecture/BUILD.md).
