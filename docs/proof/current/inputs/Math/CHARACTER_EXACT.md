# Exact-sequence character index

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Scope

This is milestone B of the representation-theoretic generalization review.
The algebraic result applies to finite-dimensional representations over any
field `k` of any monoid `G`, hence in particular of any group. It requires no
semisimplicity, invariant inner product, topology, or finite acting group.

For an equivariant linear map `f : V -> W`, the induced subspace and quotient
representations satisfy

```text
chi(ker f) - chi(W / range f) = chi(V) - chi(W).
```

These are character equalities, not representation isomorphisms or a
classification of light spectra. In positive characteristic they are
equalities of `k`-valued traces; dimension information is reduced accordingly.
The physical ordinary-Abelian no-go scope is unchanged.

## 4. Proof structure

### Algebraic Foundation

`Math/RepresentationTheory/Characters/CharacterExact.lean` imports only mathlib and the
already pinned TauCeti package. Its trace input is
`LinearMap.trace_eq_add_of_exact` from
`TauCeti.LinearAlgebra.Trace.Exact`.

- `character_eq_add_of_exact` lifts this to intertwiners in a short exact
  sequence. Only finite dimension of the middle term is assumed; the
  injectivity/surjectivity hypotheses supply finiteness of the outer terms
  in the trace proof.
- `quotientRepresentation`, `subtypeIntertwiner`, and `quotientProjection`
  construct the actual induced quotient action and its equivariant maps.
- `character_eq_sub_add_quotient` applies additivity to a subrepresentation
  and its algebraic quotient, without choosing an invariant complement.
- `rangeRestrict` and `character_eq_kernel_add_range` handle the first exact
  sequence `0 -> ker f -> V -> range f -> 0`.
- `cokernelRepresentation` is the induced action on `W / range f`.
- `indexCharacter` is the kernel character minus that cokernel character.
  `indexCharacter_eq_source_sub_target` subtracts the two exact-sequence
  identities and cancels the range character.
- `complementQuotientEquiv` identifies any supplied invariant complement
  with the quotient via its canonical quotient map. This equivalence is
  available for adapters; no complement is used in the general index proof.

### Existing Mass Interfaces

`Physics/FieldTheory/Mass/Spectrum/EquivariantMassIndex.lean` connects the previous inner-product
model to the algebraic theorem:

- `orthogonalQuotientEquiv` identifies the invariant orthogonal complement
  with the quotient representation.
- `lightIndexCharacter_eq_indexCharacter` proves the old light index is
  exactly the algebraic kernel/cokernel index for the same map.
- `lightIndexCharacter_eq_source_sub_target_of_target_unitary` drops source
  unitarity. Target unitarity still provides the invariant orthogonal
  complement used in this particular realization.
- The previous `lightIndexCharacter_eq_source_sub_target` keeps its original
  signature as a compatibility wrapper. Its virtual-character adapters and
  downstream physical proofs therefore consume the new exact-sequence proof.

The older explicit orthogonal decomposition and kernel-complement/range
equivalences are retained. They carry useful actual vector-space information
that character additivity alone does not supply.

### Symmetric Mass Extension

`InvariantWeylMass.SymmetricMass.radical_dual_character_eq` now proves

```text
chi(rad B) - chi((rad B)*) = chi(V) - chi(V*)
```

for any finite-dimensional complex group representation with an invariant
symmetric bilinear form `B`, without a norm, inner product, or unitary-action
hypothesis. It combines the new subspace/quotient character identity with
the previously proved self-duality of the nondegenerate massive quotient.
Nondegeneracy of the original form and a nonzero mass are not assumed.

The outer `InvariantWeylMass.radical_dual_character_eq` keeps its old unitary
signature as a wrapper. The existing virtual-index and physical-model
interfaces are preserved. The dual difference is still distinct from a
chosen signed Dirac index and cannot reconstruct self-dual massless sectors.

## 7. Sources and verification

### Persistent Audits

`Math/RepresentationTheory/Characters/Audit/AuditCharacterExact.lean` constructs the action

```text
a : Q,  (x,y) |-> (x + a*y, y).
```

The first-axis inclusion and second-coordinate projection form a short exact
sequence with trivial one-dimensional outer representations. The audit proves
there is no equivariant right inverse to the projection, while character
additivity and the projection/inclusion indices `+1` and `-1` still hold.
Thus the examples exercise a nonsplit extension, not just a direct sum.

`AuditInvariantWeylMass` checks the algebraic/unitary adapter, invokes the new
symmetric-mass theorem with no inner-product assumptions, and retains the
two-torsion counterexample to recovering full zero-mode spectra from dual
indices. All audited statements use only `propext`, `Classical.choice`, and
`Quot.sound`.

```bash
lake build Math.RepresentationTheory.Characters.Audit.AuditCharacterExact
lake build GUT.SU6.SelectionRules.Audit.AuditInvariantWeylMass
lake build
```

Verification at stage 01: both targeted audits passed, and the full build
completed successfully with 4234 jobs. No dependency revisions were changed.

The subsequent multiplicity-commutant and U/SU topological-centralizer
milestones are also complete. See the
[centralizer dossier](MULTIPLICITY_CENTRALIZER.md) and
[historical milestone record](../../../../topics/character-centralizer-foundations/checkpoints/generalizations.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
