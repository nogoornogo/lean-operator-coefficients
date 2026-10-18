# Finite constituent and bounded weak branching

The [continuation plan](finite-branching-plan.md) constructs complete finite
decompositions and exact support criteria without evaluating a character,
closed multiplicity, rank, matrix or exterior basis. It adds no mathematical
premise and keeps the pinned Lean/mathlib/TauCeti versions. This is a proved
finite constituent reduction; arbitrary mixed-content support entries have
not all been decided.

## Complete finite constituent criterion

[FiniteConstituentSupport](../../../Math/RepresentationTheory/Decomposition/FiniteConstituentSupport.lean)
connects the existing actual finite semisimple direct-sum decomposition to
the Hom space. `homEquiv` is an equivalence of the entire Hom with the product
of the block Homs. For an irreducible target B,

```text
Allowed(Hom_G(A,B)) iff exists i, Nonempty(Equiv_G(A_i,B)).
```

`coefficient_iff` gives the corresponding invariant coefficient test against
the dual of B. Each simple copy has positive dimension; `numberOfBlocks_le`
bounds the number of copies by the source dimension symbolically. Copies of
the same irreducible are retained separately. Empty decompositions correctly
handle a zero source.

[FiniteTensorConstituentSupport](../../../Math/RepresentationTheory/Decomposition/FiniteTensorConstituentSupport.lean)
constructs an equivalence of invariant tensor coefficients with the product
of Homs between the blocks of the second factor and dual blocks of the first.
Consequently,

```text
Allowed(Inv(A tensor B)) iff exists i j, Nonempty(Equiv_G(B_j,A_i.dual)).
```

This is a necessary-and-sufficient coupling criterion, including nonsinglets.
It does not replace the actual exterior-statistical source by unrestricted
tensor slots: its hypotheses are complete decompositions of the supplied
representations. Application to an actual content must preserve that source.

## Bounded weak SU2 labels and exact weak coupling

[SU2FiniteBranching](../../../Math/RepresentationTheory/SU2FiniteBranching.lean)
combines the existing compact complete-reducibility proof with pinned TauCeti's
`SU2.exists_nonempty_equiv_symPower`. A jointly continuous finite-dimensional
SU2 representation with torus weights bounded by N has a constructed
`Certificate`: an actual complete finite decomposition, labels in `Fin (N+1)`,
and an equivariant equivalence of each block with the indicated symmetric
power. `Certificate.equivalence` assembles a complete equivariant equivalence
from the finite sum of those symmetric powers to the original representation.

The label bound is proved, not added as a hypothesis on the decomposition.
The proof projects onto each block and transports the torus bound to that
quotient. The highest dual-basis weight excludes degrees above N. All degrees,
bases, sums and representations remain symbolic.

[SU2FiniteCoupling](../../../Math/RepresentationTheory/SU2FiniteCoupling.lean)
proves that two such complete sums have a nonzero invariant tensor coefficient
exactly when a label occurs in both sums. This uses proved symmetric-power
self-duality and TauCeti's pairwise inequivalence. No exact number of copies
or invariant coefficients is needed.

[SMFiniteWeakBranching](../../../Physics/StandardModel/Operators/SMFiniteWeakBranching.lean)
applies the complete decomposition to every actual mixed statistical source
restricted to weak SU2. Its labels are bounded by the proved doublet-slot
count. For a single signed species and degree n, `constantCertificate`
also supplies the complementary bound `min n (dimension(s)-n)`, improving the
doublet-slot bound for upper-half Q/L degrees. Thus the old coefficient cutoff
also bounds every weak constituent, including nonsinglets. This is a weak
restriction: the chosen individual copies are not asserted to be invariant
under commuting color, spin or residual actions.

## Actual local and all-degree q/l consumers

[SMFiniteConstituentSupport](../../../Physics/StandardModel/Operators/SMFiniteConstituentSupport.lean)
constructs a finite decomposition of the **whole combined compact source**
from the already proved continuous model. It preserves color, hypercharge,
weak and independent left/right spin actions together. No semisimplicity or
branching assumption is added. The source decomposition is independent of
the Higgs constituent labels m,delta.

Restriction to weak SU2 proves irreducibility of the twisted Higgs model B.
`local_allowed_iff` and `kernel_allowed_iff` then identify actual local support
with the existence of a source block equivalent to B.dual. For the existing
scalar cyclic q/l action, `original_ql_iff` states, at all h,d,

```text
Allowed(OriginalSpace(p,h,d)) iff
  charge(q,l,p)=0 and
  exists m : Fin (N_p+1), Admissible(h,d,m) and
    exists i : Fin numberOfBlocks, Matches(p,m,h-d,i).
```

`Matches` is explicitly a proposition asserting an equivalence of actual
representations. The compact comparison and q/l separation are proved, and
there is no external Weyl torus-reduction input in this theorem. It is not
an executable support classifier: the matching propositions are unevaluated.

## Remaining mixed classification prerequisite

Complete abstract finite decomposition, its source dimension bound, bounded
weak labels, and finite block/dual-block coupling are now available. The
remaining constructive step is to identify which **joint** color/weak/spin
blocks occur in each species exterior power and to decide the resulting
matching propositions, without closed numerical multiplicity certificates.

The bounded weak decomposition alone does not solve this: its choice of
weak copies need not preserve the commuting actions. The combined compact
decomposition preserves all actions but does not calculate their joint
labels or occurrence. A complete equivariant labeled exterior branching rule
with proved occurrence criteria, followed by compatible color and spin tensor
coupling rules, remains necessary for that route. No such occurrence rule has
been assumed, and no new Schur/Kronecker program has been silently started.
The present phase closes the frozen finite-constituent connections and stops
before that new labeled-branching implementation. It does not claim a complete
arbitrary mixed classification or the 572-assignment search.

The pinned library was inspected for the next bridge. TauCeti's
`ClassicalGroups/WeylModule/SchurWeyl.lean` proves a tensor-power **character**
decomposition, and `Symmetric/TensorAction/SchurWeyl.lean` proves mutual
commutants. `ClassicalGroups/WeylModule/Multiplicity.lean` identifies a
Young-ideal Hom with a GL Weyl module, with a row-count nonzero criterion.
These are useful prerequisites, not the actual mixed exterior occurrence rule.
`ClassicalGroups/Branching.lean` supplies standard block-inclusion branching;
`WeylModule/SpecialLinear.lean` explicitly does not prove irreducibility or
exhaustion after SL restriction. Thus the remaining prerequisite is a specific
joint exterior/compact-restriction connection, not a claim that Schur-Weyl or
highest-weight foundations are wholly absent from the pinned library. None of
these inspected GL modules was imported as an unproved branching assumption.

See [verification](finite-branching-verification.md) for focused proofs,
strict audits and the aggregate build boundary.
