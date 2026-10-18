# Actual SU(5) matter and branching

## 1. Result And Status

Declaration map for the established interfaces below. Actual defining, dual and
exterior-square SU(5) representations have checked irreducibility, continuous
unitary realizations and full-group SM branching.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

SU5-3a and SU5-3b: `LEAN-CHECKED`, stage 01.

## 2. Inputs And Conclusion

The representations are the actual 5, bar5 and 10, restricted along the fixed
covering map; analytic realizations use finite coordinates.

### Checked Scope

`Matter.fundamental` is the actual defining matrix action on `Fin 5 -> C`.
`Matter.antifundamental` is its algebraic contragredient, and `Matter.ten`
is its exterior square using the pinned TauCeti `Representation.exteriorPower`.
The dimensions are 5, 5, and 10. Unequal dimensions prove that `10` and
`bar5` are not representation-equivalent. Their irreducibility is proved
separately from actual SU(5) actions, as described below.

Full covering-group equivariant linear equivalences give the left-handed
branching, in units of integral hypercharge `6Y`:

```text
5    = (3,1)_(-2) + (1,2)_3
bar5 = (bar3,1)_2 + (1,2)_(-3)
10   = (bar3,1)_(-4) + (3,2)_1 + (1,1)_6
```

In the shared field conventions these are `downRight + twist weak 3`,
`downRight.dual + lepton`, and `upRight.dual + quark + electronRight.dual`.
Dropping the displayed duals changes the representation and hypercharge signs.

The exterior map is induced by the color epsilon, mixed tensor product,
and weak epsilon. Explicit wedges span each output summand; the proven
dimension equality then gives bijectivity and an inverse. No character
identity is substituted for a full-group intertwining proof.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Explicit wedges give branching inverses; coordinate projections and signed
permutations give irreducibility; kernel triviality permits quotient descent.

### Analytic Realization

`FiniteBasisUnitaryModel` is a GUT-independent adapter: continuous matrix
coefficients in a finite basis give a continuous action on a Hilbert copy.
TauCeti's `ContRepresentation.exists_isUnitary_congr` constructs an
equivalent unitary action for a compact group. The adapter proves the
representation equivalence, operator-valued continuity, joint continuity,
and inner-product preservation. An invariant form is not assumed as input.

`UnitaryMatter` supplies these coefficients from defining matrix entries,
inverse entries for the dual, and 2-by-2 minors for the exterior square.
The resulting continuous unitary models are equivalent to the three actual
algebraic representations. Their Hilbert coordinates are chosen; branching
equivalences are linear intertwiners, not asserted isometric for independently
chosen target norms.

`QuotientDescent` derives trivial action of the whole SU5-2 kernel and
constructs quotient representations on the same SM block spaces. Pullback
is exactly the original covering action. `UnitaryBranching` connects the
analytic models to this branching and gives continuous unitary quotient
actions with the same block equivalences.

### Irreducibility

`MatterIrreducibility` proves `Representation.IsIrreducible` for the actual
`fundamental`, `antifundamental`, and `ten` without irreducibility hypotheses.
The group-independent coordinate criterion says: if every invariant subspace
contains each basis component of its elements, and for every pair of basis
indices some group action has a nonzero connecting matrix coefficient, the
representation is irreducible. A nonzero subspace supplies a nonzero
coordinate; projection, scalar inversion, and mixing give every basis vector.

The SU(5) verification of these conditions is now **Lean-checked**:

1. Let `D_i` be +1 at coordinate `i` and -1 at the other four coordinates.
   These matrices are proved unitary, determinant one, and self-inverse.
   On the defining and dual bases, `1 + rho(D_i)` isolates coordinate `i`
   up to a factor 2.
2. On the exterior-square basis, `rho(D_i)` has sign -1 exactly for pairs
   containing `i`. For distinct `i,j`,
   `(1 - rho(D_i)) (1 - rho(D_j))` isolates that pair up to a factor 4.
3. A permutation matrix multiplied by its sign has determinant one in
   dimension five. Its dual/exterior action mixes the basis lines
   transitively. On the exterior square the two scalar signs cancel:
   `ten_basis_transitive` maps any ordered exterior basis vector exactly to
   any other. The extension of injective pairs to a permutation reuses
   mathlib's `Equiv.Perm.exists_extending_pair`.
4. TauCeti's `isIrreducible_of_linearEquiv` transfers all three results along
   the checked `UnitaryMatter` equivalences. Inequivalence of the unitary
   `10` and `bar5` is also checked separately by dimension.

This is irreducibility under SU(5), not under its SM subgroup. It is not a
classification of all SU(5) irreducibles. The subsequent
[SU5-4 source bridge](su5-source.md) derives residual charges/support from
actual commuting actions. The [SU5-5 endpoint](../../../applications/GUT/interfaces/su5-final.md) is now checked,
with no claim of a nonzero decay amplitude.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Module Map

| Module | Main declarations |
| --- | --- |
| [Matter](../../../../../../GUT/SU5/Representations/Matter.lean) | `fundamental`, `antifundamental`, `ten`, finrank lemmas, `ten_not_equiv_barFive` |
| [FiniteBasisUnitaryModel](../../../../../../Math/RepresentationTheory/Unitary/FiniteBasisUnitaryModel.lean) | `seed_continuous`, `model`, `modelEquiv`, `model_unitary`, `model_jointlyContinuous` |
| [UnitaryMatter](../../../../../../GUT/SU5/Representations/UnitaryMatter.lean) | coordinate continuity, three unitary models and their equivalences/dimensions |
| [BasisIrreducibility](../../../../../../Math/RepresentationTheory/Decomposition/BasisIrreducibility.lean) | group-independent `irreducible_of_basis_coordinates` |
| [MonomialElements](../../../../../../GUT/SU5/Representations/MonomialElements.lean) | actual `diagonalSign` and `signedPermutation` elements, defining action formulas |
| [MatterIrreducibility](../../../../../../GUT/SU5/Representations/MatterIrreducibility.lean) | coordinate projections, `ten_basis_transitive`, three algebraic and three unitary irreducibility theorems, unitary inequivalence |
| [Fundamental branching](../../../../../../GUT/SU5/Branching/Fundamental.lean) | `splitEquiv`, `fundamentalEquiv`, `antifundamentalEquiv` |
| [ExteriorSquare branching](../../../../../../GUT/SU5/Branching/ExteriorSquare.lean) | `branchIntertwiner`, explicit range witnesses, `branch_bijective`, `tenEquiv` |
| [QuotientDescent](../../../../../../GUT/SU5/Branching/QuotientDescent.lean) | `kernel_acts_trivially`, `descend`, `descendEquiv`, three descended block representations |
| [Unitary branching](../../../../../../GUT/SU5/Branching/Unitary.lean) | analytic branching equivalences and continuous unitary quotient actions |

`StandardModel.WeakContragredient` and `StandardModel.ExteriorPairing` now
own shared epsilon/charge lemmas. Existing names and SU(6) consumers are
preserved through imports. No six-dimensional branching module is imported
into the SU(5) construction.

## 6. Scope And Limitations

Branching intertwiners are not assumed isometries for independently chosen
norms, nor a classification of all SU(5) irreducibles.

## 7. Sources And Verification

The [scope dossier](../SM_BRANCHING.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Persistent Audit

[AuditMatterBranching](../../../../../../GUT/SU5/Audit/AuditMatterBranching.lean) rejects
transitive SU(6) imports and checks dimensions, both inverse identities,
color/mixed/weak wedge orientations, reversed weak-wedge sign, all five
left-handed hypercharges at arbitrary circle elements, complete kernel
triviality, exact quotient pullback, and the continuous unitary realizations.
It now also checks algebraic/unitary irreducibility without source hypotheses,
inequivalence, and the bottom-or-top conclusion for arbitrary actual `10`
and `bar5` subrepresentations.

```sh
lake build GUT.SU5.Audit.AuditMatterBranching
lake build
```

Targeted audit: 3821 jobs. Full regression: 4318 jobs. All 48 axiom reports
use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or
`native_decide` trust extension. The finite integer sign determinant check
uses kernel-reduced `decide`. Toolchain/dependency revisions are unchanged.
