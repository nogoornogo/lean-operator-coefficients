# Full Light-Species Qque Boundary

- ID: qque-full-species-boundary
- Status: completed
- Checkpoint detail: completed; integration tracked by Git ancestry.
- Working branch: `proof/qque-full-species-boundary`.
- Integration target: `master`.

## Frozen Endpoint

Construct Q, U and E as the full evaluation images of the standard gauge
species in a finite-dimensional SM-cover x H representation K and its dual.
Prove that every intertwiner of each specified species lands in its image.
Derive the field identifications using SM semisimplicity and multiplicity
duality; transport the complete qque classification to these full fields.
Expose both nonzero and zero criteria without positive-index assumptions.

The algebraic interface takes semisimplicity of the SM restriction, not
compactness of H. A continuous compatible radical action should discharge
that condition using compactness of the SM cover. H and its action remain
inputs. No vacuum reconstruction, exotic operator classification, derivatives,
or physical amplitudes are included. Existing sufficient-condition APIs stay
unchanged. A test on arbitrary smaller fields is not a model-wide prohibition.

## Implementation And Verification

Reuse [evaluation images](../../../Math/RepresentationTheory/Multiplicity/EvaluationImage.lean),
[multiplicity duality](../../../Math/RepresentationTheory/Multiplicity/MultiplicityDuality.lean),
[field extraction](../../../Physics/StandardModel/Gauge/LightSMFieldExtraction.lean),
and [coefficient completeness](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean).
Required gates: focused builds, strict transitive axiom audit, full build,
layout and link checks. LSP is unavailable; use targeted Lean builds.
No contraction or exchange-sign conventions change in this task.

## Result And Boundary

[FullLightSpeciesQque](../../../Physics/StandardModel/Operators/FullLightSpeciesQque.lean)
uses Q = image(K,quark), U = image(K.dual,upRight), and
E = image(K.dual,electronRight). Each image includes every intertwiner value;
the general `image_le_iff` also proves minimality. Thus the dual-side fields
are not merely arbitrary embeddings of some chosen residual constituent.
The derived `rightMultiplicityEquiv` identifies their full multiplicities
with the duals of the corresponding left-chiral multiplicities in K.

`equiv` identifies the full independent qque sector with the symmetric-square
Hom space. `nonzero_iff` gives existence and `all_forbidden_iff` gives absence.
`suppliedFieldsEquiv` and `supplied_alternation_iff` connect existing full
multiplicity field certificates without changing the older existence theorems.

[FullLightRadicalQque](../../../Physics/StandardModel/Operators/FullLightRadicalQque.lean)
specializes to the unchanged mass radical and its compatible action. SM-only
continuity suffices to derive SM semisimplicity; H may be an abstract group
with no topology. Full-action continuity is a convenient sufficient adapter,
not an extra necessary input. This does not remove compactness from the old
positive-constituent extraction theorems: classification and guaranteed
existence are different results.

The forbidden criterion concerns all multiplicities of the specified standard
Q/U/E species, with existing spinor conventions and no derivatives. It does
not classify all four-field operators, exotic species or all baryon-violating
classes. H and its compatible action remain supplied. Neither a Hom solver
nor a dynamical coupling is constructed. Smaller arbitrary field selections
cannot establish model-wide absence.

## Checks

- `lake build Physics.StandardModel.Operators.Audit.AuditFullLightSpeciesQque`:
  passes, including 19 strict transitive axiom checks. Only propext,
  Classical.choice and Quot.sound are allowed. The imported evaluation-image
  audit also passes its 22 checks.
- The [persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditFullLightSpeciesQque.lean)
  checks that retaining every scalar copy forces the full two-copy space,
  and that absence of up-left multiplicity forbids every full-sector qque
  coefficient. The latter has no topology or compactness assumption on H.
- Exact Python regressions: `audit_one_generation.py` (4), `audit_pairwise.py`
  (3), `audit_contraction_uniqueness.py` (3), all under `tools/qque/`, pass.
  They test existing contractions, not exhaustiveness of arbitrary models.
- `lake build`: passes, 5761 jobs, including the retained SU(5) and vectorlike
  benchmarks. Existing dependency warnings remain; no new warnings occur in
  the added or changed proof modules. Lean/dependency pins are unchanged.
- `node tools/layout/check-layout.mjs`: 710 modules pass.
- `node tools/docs/check-links.mjs` and `git diff --check`: pass.
- Initial direct statements caused expensive repeated model-type expansion;
  named existence predicates preserve the same propositions and reduce the
  radical wrapper build to about three seconds. The final normal build and
  axiom audit, not just the earlier direct checks, are the acceptance evidence.

No obligations remain within the frozen endpoint. Integration uses the
recorded target `master`; retain the topic branch. Git ancestry records the
actual topic and merge commits.
