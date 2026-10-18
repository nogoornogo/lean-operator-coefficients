# Actual SU(6) Radical-Index Obstruction

The [connection plan](physical-index-plan.md) is complete. The
[proof](../../../GUT/SU6/SelectionRules/Models/PhysicalIndexObstruction.lean)
excludes the five normalized Z5 light targets using an actual SU(6) action
and its invariant symmetric mass radical. It does not take the finite
matrix-index admission predicate as a hypothesis.

## Statement and physical inputs

Let R be any actual finite-dimensional complex unitary representation of
SU(6) times a commuting Abelian residual group H. Restrict it along the
standard physical torus embedding with color/weak hypercharge integers
(-2,3). Let B be any invariant complex-bilinear symmetric mass on this
restriction. Full SU(6) invariance of B is not required.

Assume the actual radical's dual character difference is the dual index
of N copies of a pure Q,U,D,L,E target, with N positive, plus any supplied
singlet index. This is the desired infrared spectrum condition, not a
primitive charge-profile equality or an assumed ultraviolet index transport.
It is weaker than an exact radical spectrum: additional vectorlike pairs
are compatible with it.

`pure_charge_equalities` derives Q=U=E as residual characters. Consequently,
`no_search_target` excludes the Yukawa-compatible search charges
Q=x, U=-x-h, D=-x+h, L=y, E=-y+h whenever 2Q-U-E is nonzero,
provided the numeric charges are mapped injectively into genuine residual
characters. The function need not be assumed additive for this exclusion:
only faithful distinction of charges is needed.

For H=Z5, `cyclicLabel` constructs the actual character
chi_q(g)=ZMod.toCircle(q*g), in additive character notation.
`cyclicLabel_injective` proves faithfulness by evaluating at the generator.
`no_normalized_target` excludes every x in Fin 5 with
Q=x, L=1-3x, H=3x-1; its qque charge is one. This holds for every positive
N and every singlet index. `normalized_dictionary` kernel-checks that these
five field charges are exactly those in the earlier finite light-profile
lists, in Q,U,D,L,E order. The theorem also excludes every other faithful
charge assignment in the original search family with nonzero qque charge.

## Proof route and reused assets

1. `PhysicalChainSource` factors the actual standard physical restriction
   through the actual SU(5) subgroup and its surjective torus cover. It
   descends the same bilinear form and identifies the actual radical; no
   inverse of the finite-kernel cover is assumed.
2. `SymmetricMassIndex.radical_dual_character_eq` derives preservation of
   the dual index: the massive quotient is equivariantly self-dual.
3. `TorusMassSource.profiles_compatible` derives the Q/U/E profile equality
   from ambient conjugation and faithful character evaluation. The mass and
   radical need not be preserved by the ambient conjugators.
4. Positive singleton profiles identify their charges, and equality of Q,U,E
   contradicts the nonzero qque charge.

The new source composes these existing proved bridges with the search
inputs. The strict transitive audit covers their dependencies as well as
the new results. No supplied formal ultraviolet character, dimension count,
Python branch table, mass rank assumption, or assumed profile equality is
used as a physical proof premise.

## Scope compared with the finite certificate

This is an alternative actual-representation certificate, not a proof that
each explicit 20,21,35,70 branching list is a continuous branching equivalence.
Those individual branching equivalences remain unproved here. They are
unnecessary for this exclusion: it covers arbitrary actual representations
with an SU(6) times H product action, including the entire selected pool
and arbitrary copies and conjugates whenever they supply such an action.
Continuity is not required by the algebraic proof; physical continuous
representations are covered if the stated hypotheses hold.

The commuting ambient residual action and standard embedding are essential
scope conditions. This theorem does not exclude a general noncommuting or
outer residual action, another embedding, a different infrared chiral target,
or all SU(6) protecting models. It proves incompatibility of the specified
actual radical index; it asserts no generated interaction or decay rate.
An exact full-gauge light equivalence can satisfy the weaker index hypothesis,
but no candidate's exact light equivalence is fabricated or assumed proved.

Verification commands and outcomes are recorded in [verification](verification.md).

For other input classes, consult the [input-axis theorem map](input-axis-theorem-map.md).
It separates this proved exclusion from routes needing additional inputs.
