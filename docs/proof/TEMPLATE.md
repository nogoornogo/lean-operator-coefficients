# Proof Dossier Conventions

## Placement By Role

Within `docs/proof/current/`, use `core/`, `inputs/` or `applications/`, then
the Math / Physics / GUT subject. Result-oriented guides live directly in
`current/` and link to these dossiers.
Concrete results outside the main claim use the appropriate input/application
role as well; keep their hypotheses and proof status intact.
Age alone is not a placement criterion. Optional input constructions are not
universal premises of the core theorem. Topics own work records, not dossiers.

## Common Reading Order

New and substantively rewritten dossiers use the following order. Omit sections
that genuinely do not apply, rather than adding empty placeholders.

1. Result and status: proved, conditional, refuted or historical.
2. Inputs and conclusion: exact hypotheses, target and theorem scope.
3. Definitions and conventions: action direction, duals, signs and normalization.
4. Proof structure: main lemmas and mathematical dependencies.
5. Lean entry points: public declarations, source files and adapters.
6. Scope and limitations: unproved premises and physical interpretation.
7. Sources and verification: reference roles, persistent audits and owning topic.

Proof dossiers and per-layer interface maps use numbered second-level sections
in this order. Interface maps summarize the input/scope and keep their detailed
declaration catalogues under Lean entry points; they supplement, not replace,
the statement dossier. Preserve old detailed heading anchors when reorganizing.
Existing detailed headings are retained as subsections where useful; legacy
single-section narratives are split at their statement/implementation boundaries.
See the [reference review](REFERENCE_REVIEW.md) for individually checked external
sources and the distinction between bibliographic checking and proof auditing.
Never infer current completion from an old build count or a historical plan.
In interface maps, keep named milestones and then-pending notes as checkpoint
context, separate from the result summary. Do not embed local work dates or
Git IDs; source publication and dependency metadata remain explicit.

## Citation Roles

Put citations where material is used, not only in a bibliography. Distinguish:

- Direct quotation: mark the quoted range and source section/page; flag any
  normalized path notation inside a quotation.
- Summary/paraphrase: explicitly identify the source of the explanation.
- Mathematical reference: explain which construction or proof route it motivates.
- External theorem input: state its hypotheses and the Lean premise it supplies;
  auditing a conditional implication does not prove the premise.
- Related document: navigation or supplementary context, not a quotation or
  an assumed theorem merely because it is linked.

Preserve existing provenance. Where attribution cannot be established, record
it as unverified instead of inventing an author, quotation or page number.
Relocation alone adds no literature input and establishes no new proof.

## Build And Path Conventions

Assume `elan`, `lake` and `lean` are on PATH. Run commands from the repository
root, where the committed `lean-toolchain` selects the pinned toolchain.
Use `lake build` and `lake env lean path/to/File.lean`, not a user's absolute
tool installation path. File links are relative to the document.

Use `<repository-root>` or `<temporary-directory>` for environment-specific
locations in examples. These are explanatory placeholders, not literal shell
arguments. Historical records are normalized too, with an explicit notice;
their recorded proof outcomes, dates and assumptions remain unchanged.

## Classification

- Math: mathematical conclusions independent of a physical interpretation,
  including concrete group/Lie-algebra constructions.
- Physics: field, mass, SM or operator results not tied to one GUT model.
- GUT: applications depending on specified unified models, matter or embeddings.
- History: superseded plans and checkpoint reviews, not current theorem dossiers.

Mixed dossiers are placed by their principal conclusion and retain links to
other layers. A concrete exceptional-group construction can belong to Math;
its named-group literature boundary or matter-model application belongs to GUT.
