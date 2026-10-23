# Upgrading From `publish/v1.0`

The development tree extends the derivative-free coefficient library from
`publish/v1.0` with derivative, equation-of-motion (EOM), integration-by-parts
(IBP) and local polynomial Lagrangian inputs. Existing nonderivative users
can continue with their input interfaces; adopting a Lagrangian is optional.

This notice compares the repository's `publish/v1.0` tag with this development
tree. It is an upgrade guide, not an announcement that a new release has
already been published.

## What Changes For Existing Users

| Area | Change and action |
| --- | --- |
| Toolchain and dependencies | Lean moves from **4.35.0-rc3 to 4.35.0**. Mathlib and TauCeti revisions change, and Physlib is added. Use the committed toolchain and manifest together, then rebuild. |
| Existing nonderivative inputs | Their mathematical inputs and coefficient operations are retained. The source refactor supplies deprecated forwarding imports and aliases for the registered public API. |
| Source layout | Implementations are subdivided by subject. Old import paths affected by this refactor forward to their canonical replacements and report migration warnings. |
| Namespaces | Shared Physics declarations move from `GUT.*` to `Physics.*`. Math declarations keep `Math.*`; model applications remain `GUT.*`. Use the replacement in each warning rather than replacing every `GUT` prefix. |
| Proof implementation | Expensive proofs have been reorganized, including structural Higgs cubature proofs. Their theorem statements and caller assumptions are preserved. No client change is needed merely because a proof body changed. |

Compatibility is a **source-level, registered-interface** guarantee. Clients
must rebuild their compiled artifacts. Private proof names, unregistered
compiler-generated helpers and reflection on the declaration kind or defining
module are outside that guarantee. See the [protected surface and checks](topics/source-api-compatibility/migration-guide.md#protected-surface).

## Migrating Imports And Names

Start by compiling the old client against the new checkout. Follow the
deprecation messages one module or namespace at a time. For example:

| Previous route | Canonical route |
| --- | --- |
| `import Math.RepresentationTheory.ProhibitionInput` | `import Math.RepresentationTheory.Protection.ProhibitionInput` |
| `Math.ProhibitionInput` | Unchanged |
| `import Physics.FieldTheory.Mass.AbelianMassSpectrum` | `import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum` |
| `GUT.AbelianMassSpectrum` | `Physics.AbelianMassSpectrum` |

The mass-spectrum example becomes:

```lean
import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum

#check Physics.AbelianMassSpectrum.exists_zeroMode_of_pos
```

The corresponding old import and name remain available with deprecation
warnings. Canonical namespaces identify the subject and ownership; they need
not repeat every directory in the module path.

The compatibility stubs are temporary and will be removed in a future
breaking release. **No removal release or date has been assigned.** The
warning marker `source-api-v1` identifies this migration, not a package or
Lean version. New code should use canonical routes now. The
[migration guide and complete mapping](topics/source-api-compatibility/migration-guide.md)
cover the remaining imports and names.

## Optional New Input Routes

| Goal | Entry and result |
| --- | --- |
| Add derivatives while keeping coefficient-style input | Import `Math.RepresentationTheory.Jets.DerivativeInterface`; use `Math.DerivativeInterface`. Graded IBP includes derivative degree zero; full-source inputs also handle EOM that mix degrees. Existing coefficients connect through `fromNonDerivative`. |
| Enter a local polynomial Lagrangian | Import `Math.RepresentationTheory.Lagrangian.StandardDensityAction`; use `Math.StandardDensityAction.model`. Supply the total density, constant linear field/direction representations and evaluated density invariance. The constructor derives Euler equations, covariance and full EOM/IBP stability. |
| Identify a model's selected fields | Import `Math.RepresentationTheory.Fields.Selection` or `Physics.FieldTheory.Fields.SelectedFields`; use `Math.FieldSelection.ofMaps` or `Physics.SelectedFields.massDictionary`. Inclusion/extraction maps and both inverse laws construct an exact retained-field dictionary. |

The derivative and density routes expose the existing coefficient/quotient
operations. Model packages also provide exact all-order coordinate equations,
reconstruction, selected-source operations and necessary/sufficient target-value criteria.
These equations can be infinite; this is not a universal finite solver.

The density route allows mixed Bose/Fermi fields and arbitrary finite
polynomial degree and ordinary derivative order. It does not accept arbitrary
analytic or nonlocal Lagrangians. Add all interactions to the **total density**
before generating EOM. A free-input classification must be checked again when
interactions change its relations.

The selected-field dictionary is an optional adapter for coefficient and jet
inputs. `Math.RepresentationTheory.Fields.JetConnection` transports odd/even
field dictionaries at all derivative orders;
`Math.RepresentationTheory.Fields.DerivativeConnection` pulls relations back
from a supplied full input. Generate interacting relations from the total
density before selecting fields. The convenience `coordinateJets`
uses one `Unit`-indexed bosonic field with trivial internal action; use
`fieldEquiv` with both field dictionaries for general bosonic content.

- [Choose a derivative/EOM route](topics/derivative-interface-adapters/input-guide.md).
- [Invariant density input](topics/euler-naturality/input-guide.md).
- [Registered models and shared operations](topics/lagrangian-model-connections/input-guide.md).
- [All-order coefficient theorem and assumptions](proof/current/core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md).
- [Selected-field inputs and execution commands](topics/model-input-connections/input-guide.md).

New [SU(6) boundary results](model-studies/su6-protection/boundary-model.md)
construct exact unmixed field amplitudes, a residual baryon action and invariant
internal contractions, and connect them to B1 coefficient prohibition. The
derivative/EOM/IBP extension takes full stable relations and a selected charge
law as inputs. Analytic mixed-mode admission and quantum protection remain
separate; these results do not certify a complete realistic boundary model.
The [standard-class obstruction](model-studies/su6-protection/feasibility.md)
uses a different light-field mechanism and retains its own hypotheses.

Additional complete coefficient classifications cover specified free scalar,
Higgs and one-flavor Weyl–Higgs sectors. Their complex dimensions are,
respectively, **1, 3 and 1** at four fields/four derivatives for the scalar
and Higgs cases, and two odd fields/four even fields/one derivative for the
Weyl–Higgs case. See the
[scalar](topics/scalar-quartic-four-completeness/results.md),
[Higgs](topics/higgs-quartic-four-completeness/results.md) and
[Weyl–Higgs](topics/weyl-higgs-current-completeness/results.md) statements
for their precise actions, free equations and full-relation selections.
They are individual sectors, not a complete interacting EFT classification.

The earlier **572-input, 326 allowed / 246 forbidden** cyclic SM/Higgs
classification is retained. Its exact minimum dimensions remain
**derivative-free** minima; the new derivative interfaces do not extend that
minimum claim automatically. See the [classification scope](proof/current/DECIDABLE_CLASSIFICATIONS.md).

## Rebuilding A Client

Use the new checkout's committed `lean-toolchain`, `lakefile.lean` and
`lake-manifest.json` together. From its repository root:

```sh
lake exe cache get
lake build
lake env lean -j2 <client-file.lean>
```

Replace `<client-file.lean>` with the client source path. If another Lake
project depends on this library, update its library revision and toolchain
deliberately, then rebuild that project as well. Do not copy old `.olean`
artifacts across toolchains or run `lake update` as a routine reproduction step.

[Build instructions](architecture/BUILD.md) distinguish incremental cache
reuse from fresh source compilation. The
[proof-memory audit](topics/proof-memory-audit/README.md) and
[Higgs cubature refactor](topics/higgs-cubature-structure/README.md) record
the bounded performance measurements; they are not universal resource bounds.
