# Self-dual sources and light chirality

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Scope

**DUAL-1 and DUAL-2 are LEAN-CHECKED.** A finite-dimensional complex source with an
actual equivariant self-duality has zero restricted dual character.
The same conclusion follows from pointwise ambient conjugacy of each
tested subgroup element to its inverse. A single normalizer implementing
inversion is a sufficient special case. Every invariant complex-bilinear
symmetric mass on that subgroup preserves this zero dual index in its
radical, by the existing massive-quotient theorem.

The source self-duality or conjugacy condition remains explicit. No
compactness, unitarity, irreducibility, topology, or Laurent realization
is needed by these algebraic lemmas. Character restriction itself works
over any field; the mass endpoint uses the existing complex mass API.
Finite signed sums of source characters also satisfy inversion invariance,
but are not treated as vector spaces on which a physical mass acts.

Zero dual index does not mean there are no light fields, nor that every
self-dual representation admits a nondegenerate symmetric mass. Gauge
self-duality does not automatically imply charge-resolved self-duality.
The target bridge now excludes the specified positive SM dual light target.
This is not a classification of compact groups. The
[SP-1/2 application](../GUT/COMPACT_SYMPLECTIC_CHIRALITY.md) now proves actual
inverse conjugacy for all compact symplectic elements. It excludes the
positive target for arbitrary subgroup restrictions with the declared
faithful target evaluator, not only for the chosen SU(5) chain.
The independent Spin(10)/E6 selection-rule branches remain in
the [extension plan](../../../../topics/self-dual-chirality/plans/SELF_DUAL_AND_AMBIENT_GROUP_PLAN.md).

## 4. Proof structure

### Positive SM Target

For any additive Abelian charge-label group, forgetting charges commutes
with the dual difference. At each of the fifteen oriented SM gauge weights,
the forgotten target coefficient is the common generation total N. Neither
the opposite gauge weights nor singlets contribute to that coefficient.
Thus N > 0 makes the gauge dual target nonzero, including torsion charges
and arbitrary finite charge distributions.

The generic evaluator uses distinct actual complex characters of a supplied
test group; its faithfulness follows from character independence. Only the
target has a finite weight model. The mass theorem excludes that target
when the source character equals its dual on the tested gauge group.
Equivariant source self-duality and ambient inverse conjugacy each supply
that equality, without requiring mass invariance under the whole ambient
group.

The standard-chain adapter constructs the actual SU(5) torus weight
characters and proves that evaluating the forgotten polynomial is exactly
the existing charge-resolved evaluator at residual identity. Consequently,
`StandardChain.Model` cannot be inhabited by a gauge-self-dual source, or
by a source whose tested gauge torus is inverted by ambient conjugation.
This uses the model's existing exact dual target, not an additional
coefficient or radical-index assumption. The earlier physical-SM torus
identification remains in force.

This is a spectrum-existence obstruction, distinct from the ordinary
Abelian operator-selection obstruction. The previous SU(N) results and
their assumptions are unchanged; general SU(N) sources are not assumed
self-dual.

### Persistent Controls

- An actual equivariant self-duality of the sign line over the order-two
  group of integer units is constructed from its bilinear pairing.
- Zero mass on that line has zero dual index and a nonzero radical.
- Its nonzero invariant mass also has zero dual index.
- Every finite-dimensional representation of the non-Abelian permutation
  group on three points satisfies the pointwise inverse-conjugacy test.
- The usual U(1) character at zero mass has a provably nonzero dual index,
  so the additional source condition cannot be dropped.
- The combined audit rejects transitive SU(5)/SU(6) imports.

DUAL-2 adds a mixed ZMod 2 charge-family example with coefficient 3,
arbitrary singlets, vectorlike-pair invariance, and a zero-generation
control where the forgotten dual target is zero. An actual charged gauge
singlet demonstrates that gauge self-duality does not imply residual-charge
self-duality. The actual positive SU(5) benchmark is proved not gauge
self-dual, including its order-two charged specialization.

The DUAL-2 coefficient audit permits the two existing SU(5) weight-combinatorics
modules, but rejects SU(5) group/source modules and all SU(6) imports. The
separate physical-torus adapter uses SU(5) and rejects SU(6).

Declarations and verification are in the
[formalization record](../../inputs/Math/interfaces/self-dual-chirality.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
