# General character restriction obstruction

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Milestone A completed and regression-checked at stage 01.

### Scope

This is milestone A of the representation-theoretic generalization review,
not the original semisimple embedding-classification lemma A.

Let `G` be any group, `k` any field, `T` a parameter type, `incl : T -> G`,
and `action : T -> T`. Suppose an element `n : G` satisfies

```text
incl (action t) = n * incl t * n^-1
```

for every `t`. Every finite integer combination of finite-dimensional
`k`-representation characters restricts to an `action`-invariant function.
Consequently a non-invariant target is outside the restriction image.

Neither injectivity of `incl` nor a group structure on `T` is required.
There are no compactness, continuity, unitarity, or semisimplicity assumptions.
The basic trace-invariance lemma itself does not require finite dimension;
the finite-virtual interface explicitly requires it.

This is a necessary-condition obstruction. Invariance is not asserted to be
sufficient for a lift. The statement is about characters, not classification
of representations by characters or a construction of a Grothendieck ring.

## 4. Proof structure

### SU(6) Connection

The existing theorem interfaces are retained:

1. `ActualRestriction.restrictedCharacter_swap36_fixed` now instantiates
   `character_restriction_invariant` with the proved signed permutation
   conjugation formula.
2. `VirtualRestriction.FiniteVirtualSU6Representation.toCharacterCoefficients`
   maps existing finite presentations to `FDRep` coefficients, adding repeated
   identical objects. `virtualRestriction_eq_restrictedCharacter` proves
   exact agreement with the original trace function. The original
   `restrictedCharacter_swap36_fixed` then uses the generic finite-virtual
   invariance theorem.
3. `NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed`
   applies `not_mem_range_of_nonfixed_model` using the already proved
   normalized Laurent faithfulness and `swap36` evaluation compatibility.

No physical scope is enlarged by these adapters. The concrete embedding,
Weyl representative, faithful target evaluator, and SM non-invariance are
still the SU(6)-specific inputs.

### Related Completed Generalizations

[Exact-sequence character additivity](CHARACTER_EXACT.md) now supplies the
kernel/cokernel index while retaining the physical adapters.
[Multiplicity centralizers](MULTIPLICITY_CENTRALIZER.md) now include the
actual U/SU topological classifications. Their completed milestones and
boundaries are recorded in the [historical milestone record](../../../../topics/character-centralizer-foundations/checkpoints/generalizations.md).

## 5. Lean entry points

### General API

`Math/RepresentationTheory/Characters/CharacterRestriction.lean` imports only mathlib.

- `character_restriction_invariant` is the direct consequence of
  `Representation.char_conj` and the conjugation equation.
- `virtualCharacter` uses `Finsupp I Int` coefficients with a possibly infinite
  index type and a family of actual finite-dimensional representations on
  possibly different vector spaces. Finite support limits the sum.
- `virtualCharacter_restriction_invariant` and
  `not_mem_virtualRestrictionImage` prove invariance and exclusion for every
  such family and every finite signed combination.
- `virtualRestriction` indexes the coefficients by all mathlib `FDRep k G`
  objects. `not_mem_finiteVirtualRestrictionImage` excludes targets from
  this whole finite-virtual character image, rather than from a chosen
  generating family alone. `FDRep` uses mathlib's carrier-universe convention;
  the family version also permits a separate carrier universe.
- `fixed_of_faithful_eval` reflects function invariance through an injective
  evaluator that intertwines the target-model and parameter-space actions.
- `not_mem_range_of_nonfixed_model` excludes a nonfixed modeled target from
  any invariant family of source functions. Its representation specialization
  is `not_mem_virtualRestrictionImage_of_nonfixed_model`.

Faithfulness is needed only for the target model. No Laurent polynomial or
weight decomposition is required for the source representations. Integer
coefficients are evaluated in `k`; in positive characteristic this is still
an obstruction at the level of `k`-valued trace functions, not a faithful
integer representation-ring invariant.

## 7. Sources and verification

### Persistent Audit

`Math/RepresentationTheory/Characters/Audit/AuditCharacterRestriction.lean` checks:

- a non-invariant function on the permutation group of three points, excluded
  for every family of finite-dimensional rational representations;
- a realizable constant character expressed using coefficients `2` and `-1`;
- the obstruction for a noninjective parameter map;
- a nonfaithful compatible evaluator whose nonfixed model evaluates to a
  realizable invariant character, showing why faithfulness cannot be dropped.

The audited generic statements and examples use only a subset of `propext`,
`Classical.choice`, and `Quot.sound`. The existing flipped audit additionally
checks the coefficient adapter and the downstream SU(6) endpoints.
Full regression build: `Build completed successfully (4230 jobs)`.

```bash
lake build Math.RepresentationTheory.Characters.Audit.AuditCharacterRestriction
lake build GUT.SU6.SelectionRules.Audit.AuditFlippedWeylObstruction
lake build
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
