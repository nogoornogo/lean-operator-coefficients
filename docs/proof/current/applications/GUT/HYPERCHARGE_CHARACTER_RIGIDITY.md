# Hypercharge character rigidity

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

`LEAN-CHECKED DEGREE-FIVE CORE AND ACTUAL TORUS-TARGET BRIDGE FOR FINITE-DIMENSIONAL JOINTLY CONTINUOUS SOURCES`

## 3. Definitions and conventions

The dual-index convention is now supported independently of full-spectrum
reconstruction. `PhysicalWeylMomentBridge` proves that duality negates the
fifth moment and antisymmetrization doubles it. Equality with the dual SM
target therefore still forces `(-2,3)`. A faithful Fourier bridge covers
actual continuous-unitary source traces. `PhysicalWeylChargeBridge` uses
one resolved dual target for both this hypercharge character rigidity conclusion and normalized standard charge-orbit bridge -> Abelian proton-operator neutrality,
with arbitrary Abelian charges. `PhysicalWeylMassSource` now derives this
target from canonical actual fields and the mass radical at arbitrary
cocharacters; self-dual sectors are not recovered. The continuous-geometry
assembly is recorded in [the Weyl model dossier](../../inputs/GUT/WEYL_MODEL.md).

A proposed representation-ring / Weyl argument claims that, for an exact SM-only chiral family, all possible hypercharge embeddings collapse to two branches:

1. standard:
   \[
   6Y=(-2,-2,-2,3,3,0),
   \]
2. flipped:
   \[
   6Y=(1,1,1,0,0,-3).
   \]

## 4. Proof structure

**Lean update:** `GUT/SU6/Hypercharge/HyperchargeBranchArithmetic.lean` starts from the
actual physical-centralizer cocharacter lattice checked in hypercharge centralizer geometry.  For an
injective circle, primitivity of its integer pair is Lean-checked.  A
primitive circle with an oriented neutral defining block is standard or
flipped once the distinct color-neutral pair is excluded.  Weak neutrality
gives the flipped pair and singlet neutrality gives the standard pair, in
each case up to circle orientation.

Primitive neutral-block arithmetic alone has a third possibility, the
color-neutral pair `(0,1)` up to sign.  This branch is now independently
excluded at the physical-character level.  `GUT/SU6/SelectionRules/FlippedBranch/ColorNeutralSMGroup.lean`
constructs the injective block embedding `SU(3) x U(2) -> SU(6)` and lifts its
diagonal torus.  `GUT/SU6/SelectionRules/FlippedBranch/ColorNeutralSMTarget.lean` realizes the five SM
fermion multiplets as actual finite-dimensional representations of this
group and identifies their finite virtual trace character with the normalized
Laurent target.  `GUT/SU6/SelectionRules/FlippedBranch/ColorNeutralBranch.lean` proves that target is not
fixed by the `(5 6)` Weyl transposition, whereas every finite virtual `SU(6)`
restricted character is fixed.  Hence the color-neutral one-generation SM
target cannot be an `SU(6)` restriction; the Laurent-level result also covers
every nonzero integer generation count and arbitrary gauge singlets.

There is now a second, stronger route which does not assume a neutral defining
block.  `GUT/SU6/Characters/DegreeFiveWeylInvariant.lean` proves that every symmetric
homogeneous degree-five polynomial in six variables restricts to the
trace-zero Cartan as
\[
A p_5+B p_2p_3.
\]
`GUT/SU6/Characters/AmbientWeylMoment.lean` represents a finite virtual ambient weight
character by an integer-valued `Finsupp` on canonical rational trace-zero
weights.  It proves that full `S_6` invariance makes the fifth weight-moment
polynomial symmetric and homogeneous, and hence puts that moment in the span
above.  `GUT/SU6/Characters/FifthMomentHypercharge.lean` computes the one-generation SM
fifth moment and proves by exact rational identities that its restriction can
have this form only for the standard cocharacter pair `(m,n)=(-2,3)`.  The
same conclusion holds for every nonzero rational generation multiplicity.

This is the third checked milestone: the normalized finite-weight algebra,
the degree-five invariant theory, and the cocharacter arithmetic are all
kernel-checked and collected in `GUT/SU6/SelectionRules/Audit/AuditHyperchargeStandard.lean`.
The subsequent hypercharge character rigidity bridge layer is now also checked.  The canonical integral
ambient weight lattice is `Fin 5 -> Integer`; its Laurent evaluator on the
actual determinant-one diagonal torus is faithful.  Given only an
`ActualAmbientLaurentModel`, trace conjugacy by signed Weyl representatives
proves full `S_6` invariance rather than assuming it.  The result is closed
under finite integer virtual combinations and maps to the rational
finite-weight model used by the fifth-moment theorem.  Continuous characters
of every finite-dimensional compact torus are independently identified with
integer exponent vectors.

`GUT/SU6/Characters/AmbientTorus.lean` now realizes `Circle^5` as the actual
determinant-one diagonal torus and proves that its integer characters evaluate
as the canonical normalized Laurent monomials.  In
`GUT/SU6/Characters/ContinuousUnitaryWeightDecomposition.lean`, restriction of any
finite-dimensional jointly continuous unitary `SU(6)` representation to this
torus is decomposed into finitely many simple blocks.  Commutativity makes
each block one-dimensional; continuity and unitarity identify its scalar
action with a unique integral weight.  The resulting finite `Finsupp`
polynomial is proved, by a basis trace calculation, to evaluate to the actual
restricted character.  This supplies `ActualAmbientLaurentModel` directly for
the continuous-unitary scope and for finite virtual combinations, and it
transfers along any supplied continuous-unitarizable representation
equivalence.  These results are audited in `GUT/SU6/SelectionRules/Audit/AuditHyperchargeCharacterRigidity.lean`.

`GUT/SU6/Adapters/CompactRepresentationUnitarization.lean` removes the unitary
hypothesis from the supplied source.  It normalizes Haar measure on the actual
compact maximal torus, averages an arbitrary seed Hermitian inner product,
proves positivity and torus invariance of the averaged form, and puts the
resulting norm on a fresh representation-indexed copy.  Finite-dimensional
automatic continuity proves that both comparison maps are continuous, so the
transported torus action is jointly continuous and unitary.  The existing
integer-weight decomposition then constructs an `ActualAmbientLaurentModel`
for every finite-dimensional complex `SU(6)` representation on a normed inner
product space whose action is jointly continuous.  No invariance of the seed
inner product is assumed.  Heterogeneous finite integer virtual combinations
are packaged by `FiniteContinuousVirtualRepresentation`, and their common
Laurent polynomial is proved fully Weyl invariant.

`GUT/SU6/SelectionRules/Models/ContinuousPhysicalSourceBridge.lean` feeds this non-unitary source
scope directly into the exact finite-weight, physical-torus function, and
representation-character-equivalence versions of the fifth-moment theorem.
Thus all three existing hypercharge character rigidity target formulations force the standard
cocharacter without assuming that the source representations arrived with
unitary actions.  The new path and its finite-virtual specialization are
included in `GUT/SU6/SelectionRules/Audit/AuditHyperchargeCharacterRigidity.lean`; their only reported logical dependencies
are `propext`, `Classical.choice`, and `Quot.sound`.

`GUT/SU6/Characters/PhysicalFifthMomentBridge.lean` closes the next source step without
using an exposed list polynomial.  It pushes the canonical ambient `Finsupp`
character to a rational physical-weight `Finsupp`, with `mapDomain` summing
all restriction collisions.  Lean computes the fifth moment of the explicit
fifteen left-handed Standard Model weights and proves it equals
`smFifthMoment`; arbitrary virtual multiplicity at physical weight zero is
allowed for gauge singlets and contributes zero.  Therefore an exact
SM-plus-singlets chiral-character restriction with any nonzero integer
generation count supplies
`HasSMFifthMoment` and forces `(m,n)=(-2,3)`.  The theorem is instantiated
directly for every finite virtual collection of actual finite-dimensional
jointly continuous unitary `SU(6)` representations through its common
`VirtualAmbientLaurentModel`.  These declarations are also permanently
audited in `GUT/SU6/SelectionRules/Audit/AuditHyperchargeCharacterRigidity.lean`.

`GUT/SU6/Characters/PhysicalTorusCharacterBridge.lean` removes the internal finite-weight
equality as a primitive source assumption.  For every integral pair `(m,n)` it
constructs the actual compact physical four-torus inside the ambient diagonal
torus, proves monomial-by-monomial compatibility with integral weight
restriction, and proves the four-variable Fourier evaluator faithful.  Thus
pointwise equality on this torus between the actual finite virtual restricted
character and the explicit SM-plus-singlets target implies the exact
`Finsupp` equality above.  In particular, a finite virtual collection of
actual jointly continuous unitary sources with a nonzero number of generations
and this function-level physical character equality forces the integral pair
`(m,n)=(-2,3)`.

`GUT/SU6/Branching/PhysicalSMTorusTarget.lean` now realizes the right-hand side of that
function equality representation-theoretically.  Every integral physical
weight gives an actual one-dimensional representation of the multiplicative
compact four-torus, and every finite integral `Finsupp` character is realized
as their finite virtual sum.  In particular, the exact SM-plus-singlets
character is an actual finite virtual target with trace character equal to the
faithful Fourier evaluator.  The file also constructs the physical-torus group
homomorphism into the actual determinant-one diagonal `SU(6)` torus and proves
that character equivalence between this target and the restriction of an
actual finite virtual `SU(6)` source forces `(m,n)=(-2,3)`.  The theorem is
instantiated for finite virtual jointly continuous unitary sources and is
permanently audited in `GUT/SU6/SelectionRules/Audit/AuditHyperchargeCharacterRigidity.lean`.

The hypercharge character rigidity source bridge is therefore closed for the explicit analytic scope used
by the new source structure: finite-dimensional complex normed inner-product
spaces with a jointly continuous `SU(6)` action.  A future formal category of
smooth or algebraic representations would still need a theorem forgetting its
extra structure to this jointly continuous scope; no such source category is
currently part of the project.  This is a scope-typing issue, not a remaining
unitarization premise in hypercharge character rigidity.  Separately, the final physical model interface
must supply the now-checked character equivalence between its restricted
finite virtual source and the actual SM-plus-singlets torus target from its
SM-only chiral spectrum hypothesis; Lean no longer assumes a derived
`Finsupp`, fifth-moment, or bare evaluator identity directly.  The older
neutral-block implication is an alternative route, not an assumption of the
new checked classification.

---

## 7. Sources and verification

**Audit requirement:** this classification must be independently reconstructed. Do not rely on the conversational derivation.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
