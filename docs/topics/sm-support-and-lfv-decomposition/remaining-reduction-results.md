# Remaining Reduction: Descent Interfaces and Group-Action Boundary

The continuation proves two exact descent interfaces and an actual SM
fixed-content consumer. It does **not** complete their composition into the
previous split weak-singlet reduction, nor the nontrivial weak-source
classification. This is a verified intermediate checkpoint and a scoped
feasibility stop, not completion of all remaining support work.

## Proved full-field connection

[TypedSymmetricPatternHom](../../../Math/RepresentationTheory/TypedSymmetricPatternHom.lean)
works with a finite species alphabet, arbitrary complex species modules,
actual group representations and an arbitrary equivariant output module.
Its full carrier is the symmetric power of the entire species field sum.
The selected coefficient subspace vanishes on every pure species word whose
labels are outside the permutation orbit of a specified pattern.

Restriction to that pattern is a linear equivalence to typed multilinear
maps satisfying actual equivariance and compatibility under every permutation
preserving the pattern. Reconstruction sums permutations and divides by the
pattern stabilizer cardinality. Both inverse identities are proved; neither
an embedding nor a dimension equality is substituted for surjectivity.

The source consumer curries invariant scalar coefficients into maps valued
in the source's algebraic dual. `sourceSpace_iff` proves that its selected
submodule means exactly vanishing on other scalar contents for every source
vector. The source can already be an exterior-power carrier, so its statistics
are preserved. No weak triviality, seed, nonzero coefficient, finite source
dimension or semisimplicity premise is added.

[HiggsPatternDescent](../../../Physics/StandardModel/Operators/HiggsPatternDescent.lean)
instantiates this equivalence with the original `BnvMixedInput` Higgs and dual
fields, neutral one-dimensional scalar multiplicities and an arbitrary exterior
power of the actual ten signed SM species with supplied flavor actions. Its
`allowed_iff` and `forbidden_iff` transport coefficient predicates exactly.
These are equivalences of presentations, not arithmetic support classifiers.
They apply to nontrivial weak sources as well as weak-singlet ones.

## Proved split-field connection

[TwoBlockSymmetricDescent](../../../Math/RepresentationTheory/TwoBlockSymmetricDescent.lean)
constructs a linear equivalence between

    Hom_G(X tensor (Sym^h B tensor Sym^d D), C)

and source-linear maps to nested multilinear forms, separately symmetric in
the B and D slots and invariant under the simultaneous actual group action.
It handles distinct module types B and D and arbitrary source X. Descent
through both symmetric quotients and both inverse identities are proved.

This does not by itself identify the typed pattern subspace above with this
nested symmetric space. That joining theorem is still required before the
previous split weak-singlet support iff can be claimed for the original
full-field selected subspace. In particular, the new SM `allowed_iff` does
not assert allowance iff balanced counts and a zero-Higgs coefficient exists.

## Exact remaining join

For the canonical pattern with h Higgs and d dual slots, the needed proof is
a linear equivalence between the typed, pattern-compatible maps and the
nested separately symmetric maps. It must prove both directions of the
permutation condition, handle dependent species carrier reindexing and
preserve source/group actions. Matching evaluations or identifying a common
raw tensor does not supply that equivalence. This is an algebraic connection
obligation, not an external literature premise.

## Nontrivial weak-source feasibility stop

The pinned TauCeti Sl2 Clebsch-Gordan file provides Lie-algebra modules and
Lie-module equivalences. The SU2 completeness file supplies a character
recursion, not the needed actual tensor-carrier equivalence. SU2 symmetric
power irreducibility is already directly reused in the preceding result.
SU2 exhaustion concerns continuous irreducible representations and does not
automatically identify the fixed tensor decomposition here.

The missing prerequisite is an actual SU2-equivariant decomposition of
Sym^h H tensor Sym^d Hdual, together with source constituent connections and
the retained other group actions. A new Lie/group integration bridge or an
algebraic group-level Clebsch-Gordan proof is needed before using the inspected
Lie algebra result to close this route. No character equality, spectrum
count or missing seed is promoted to an operator support theorem.

The [contract](remaining-reduction-contract.md) stops that foundational route
here. The algebraic join above remains explicitly unfinished. Complete SM
support classification, general nontrivial-source finite reduction and a
maximum primitive Higgs degree are not proved. No new UV, VEV, mass, anomaly,
matching, rate, dependency or heartbeat assumptions are introduced.

## Verification

All 33 new Math and seven Physics public declarations are registered in the
existing strict transitive audits. The [verification record](verification.md)
records the focused checks and full build. This work remains on the approved
topic branch; no master merge or push is authorized.

## Subsequent SU2-only proof

The user subsequently authorized the limited group-level foundation.
[SU2 tensor decomposition](su2-clebsch-gordan-results.md) now discharges
that prerequisite without using Lie/group integration or character equality
as an equivalence premise. The preceding stop describes this checkpoint's
scope, not a continuing missing SU2 theorem. The typed/split join and other
SM-action connections remain separate obligations.

## Subsequent full-group and full-field connection

[Full Higgs connection](full-higgs-connection-results.md) now proves the
original fixed scalar-count/full-carrier equivalence to split symmetric powers
and retains the actual SM hypercharge factor in every weak constituent.
This closes those presentation/action obligations from the earlier checkpoint.
Classification of every fermion source's invariant Hom support, and a uniform
all-degree reduction for all contents, remain separate obligations.
