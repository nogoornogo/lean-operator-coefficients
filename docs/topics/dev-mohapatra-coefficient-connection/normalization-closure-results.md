# Nonzero Action and Normalization Closure

The [frozen plan](normalization-closure-plan.md) is complete. The
[Lean source](../../../Physics/StandardModel/Operators/DevMohapatraNormalizationClosure.lean)
connects the all-degree projected action with a concrete nonzero operator
and classifies matching within an explicit multiplicative parameter family.

## Actual action inequality

`coordinates_fields` transports all eighteen independent selected components
to the previous species/color/spin carrier. Its checked six-component exterior
witness proves `operator_nonzero` for the actual lower-block literature
operator on the all-degree projection carrier. No nonzero-operator premise
is supplied externally.

For nonzero scalar quadratic mass, Majorana mass and both selected couplings,
`action_ne_paper` and `ordered_action_ne_paper` prove that the exact projected
Hermitian action differs from the action obtained using the literal positive
Eq.(4) scalar and the same literature operator. This excludes accidental
vanishing of the operator as an explanation for the coefficient comparison.
The original scalar UV-action connection additionally uses the existing
nonzero real scalar quadratic parameter condition.

## Matching condition

Let m denote the printed scalar mass squared, M the Majorana mass, lambda
and z the printed selected couplings, and O the fixed nonzero literature
operator. Supply these identifications:

| Component/action quantity | Identification |
| --- | --- |
| Scalar quadratic parameter | mu * m |
| Majorana mass | nu * M |
| First component vertex | a * lambda |
| Selected down vertex | b * z |
| Comparison operator (including any overall action sign) | t * O |

For nonzero original masses/couplings and nonzero mu, nu,
`normalization_match_iff` proves the necessary **and sufficient** condition
for the projected component action to equal `paperPrefactor * (t O)`:

```
-8 pi² (a b)² = t mu² nu.
```

The coefficient ratio before operator rescaling is
`-8 pi² (a b)² / (mu² nu)`. The ordered no-half interpretation is included
by setting b = 2, yielding the earlier -32 pi². A flavor half returns b = 1.
The theorem allows complex multipliers and even zero t or vertex multipliers;
usable invertible dictionaries require them to be nonzero as well.

With canonical masses and both vertex identifications fixed (mu=nu=a=b=1),
matching requires t=-8 pi². With the operator fixed instead (t=1), the
vertex product must satisfy `(a b)²=-1/(8 pi²)`. An overall Hamiltonian sign
can change the signed condition, but still leaves a magnitude compensation.
These are conditional algebraic requirements, not evidence that the paper
uses such factors or that an arbitrary operator normalization is physical.

## Consistent convention changes

The multipliers above describe independently supplied source/component
identifications. They do not certify the kinetic normalization or form a
classification of arbitrary field redefinitions.

`consistent_bilinear_match_iff` separately handles the already proved common
bilinear convention change: mass and both vertices acquire c, and the
three-bilinear operator acquires c³. For nonzero c, matching after that change
is equivalent to matching before it. Thus this consistent convention change
cannot absorb the discrepancy. Changing only the target operator would be
an independent source identification, not that common convention change.

## Boundary

The conditional action inequality is now proved, and the compensating
normalization requirements are explicit. Whether the target supplies any
such identification remains a documentary/physical matching question.
Neither theorem certifies a paper error or determines an undocumented
normalization. No new external literature premise, loops, rates, additional
N/flavors, merge or push is included.
