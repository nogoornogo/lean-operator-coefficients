# Invariant Mass Protection

- ID: invariant-mass-protection
- Status: completed
- Checkpoint detail: completed (integration recorded by Git).
- Working branch: `proof/invariant-mass-protection`.
- Integration target: `master`.
- Result type: necessary/sufficient algebraic classification.

## Frozen Endpoint

Fix a representation V, its invariant symmetric mass B and L = radical B.
For an additional representation W classify all invariant symmetric masses
on V x W restricting to B. Prove individual radical preservation iff the
cross mass vanishes on L x W; universal preservation iff every intertwiner
V -> W.dual restricts to zero on L. With an equivariant retraction, prove
equivalence to all intertwiners L -> W.dual being zero. Reuse semisimple
splitting and common-simple-constituent criteria. Include arbitrary indexed
families as a consumer for future UV-generated masses.

No new UV model, Yukawa/vacuum construction, changing base radical, exact
full light-spectrum identification or amplitude claim. Do not identify
abstract invariant couplings with UV-realizable ones. No new axioms or pins.
Complete and integrate this topic before the separately authorized certificate
abstraction. Stop on a mathematical obstruction or scope-changing prerequisite.

## Interfaces

- [Mass and radical](../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean)
- [Boundary counterexample](../light-inheritance-boundary/README.md)
- [Semisimple splitting](../../../Math/RepresentationTheory/Decomposition/SemisimpleSplitting.lean)
- [Common constituents](../../../Math/RepresentationTheory/Decomposition/CommonIrreducible.lean)

## Results

[InvariantMassProtection](../../../Physics/FieldTheory/Mass/InvariantMassProtection.lean)
constructs the equivariant cross map of any invariant mass on V x W, and
constructs a symmetric invariant block mass for EVERY intertwiner V -> W.dual,
with fixed B and arbitrary invariant W mass D. `cross_block` recovers the
chosen intertwiner exactly. Thus universal quantification is over actual
invariant symmetric masses extending B, not a tautologically defined class
of maps on L which might fail to extend to V.

- `preserves_iff`: the original radical, included by x -> (x,0), survives iff
  the cross map composed with its inclusion is zero.
- `radicalMap` and `radicalMap_injective`: preservation gives an actual
  equivariant injection of radicals, retaining the full G action.
- `universal_iff_restriction`: protection against every invariant symmetric
  extension iff every ambient intertwiner restricts to zero on L.
- `universal_iff_hom_zero_of_retraction`: with a supplied equivariant
  retraction V -> L, this is equivalent to Hom_G(L,W.dual) being zero.
- `universal_iff_hom_zero`: semisimplicity of V derives that retraction.
- `universal_iff_no_common`: semisimplicity of V also derives semisimplicity
  of L; protection is equivalent to absence of common simple submodules of
  L and W.dual. No semisimplicity assumption on W is required.
- `exists_lifting_iff_common`: in the same scope, a common constituent is
  equivalent to existence of a mass extension that fails to retain all of L.
  This is an existence assertion, not lifting for every coupling.
- `family_iff`: arbitrary indexed mass families extending B satisfy the
  pointwise restriction criterion. P need not have linear/topological structure.

The strict audit also rechecks the previous paired-dual counterexample through
the NEW universal-protection predicate. There is no topology, compactness or
finite-dimensionality premise in these algebraic results. A retraction or
semisimplicity is used only where stated. No claim is made that L exhausts the
new radical or that a rotated replacement light space cannot survive.

The family interface is ready for a future UV-generated family, but this
topic does not construct one or assert that all invariant couplings arise
from a specified UV theory. The mediator-to-qque certificate is a separate
topic and is not a consequence of radical inclusion alone.

## Verification

- Focused `lake build Physics.FieldTheory.Mass.Audit.AuditInvariantMassProtection`:
  passed, 16 strict transitive checks allowing only propext, Classical.choice,
  Quot.sound. Initial elaboration errors were fixed; no new source warnings.
- Full `lake build`: passed, 5837 jobs (existing dependency warnings replayed).
- Layout: passed, 786 modules. Links: passed, 297 Markdown files, 1792 links,
  33 fragments. `git diff --check`: passed.
- Lean LSP unavailable; used source inspection and builds.
- No qque coefficient/sign/statistics definitions changed; exact qque scripts
  are not rerun for this mass-only topic.
- Commit and no-ff merge to master, retain branch, no push. Recheck merged state.
