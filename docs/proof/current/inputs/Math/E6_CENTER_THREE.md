# Order-Three Center and the Actual 27

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Finite Deliverable

After `checkpoint 01`, the user requested progress on the remaining global-form
obligation. The actual candidate-group model is already inhabited. This
package addresses a concrete global-form constraint, not another E6-0
feasibility phase or an assertion of the full intended identification.

1. Use the existing Cartan grading coefficients `[4,3,5,6,4,2]` and proved
   weights `1,-2,4` to construct a real-form element whose exponential is
   `exp(2*pi*I/3)` times the 27-dimensional identity.
2. Prove actual identity-component membership, centrality, exact order
   three and the resulting center-cardinality lower bound. Relate this to
   the ninth power of the already constructed order-27 full-normalizer scalar.
3. Prove that the actual 27 acts nontrivially on this central element and
   cannot descend to the quotient by the candidate's center. This guards
   against replacing the carrier by a central quotient without checking
   whether the matter representation survives.
4. Persistent standard-axiom audit, full build, documentation and commit.

Modules: `Minuscule/CenterThree`, `Minuscule/CentralQuotientObstruction`
and `Audit/AuditCenterThree`. Reuse the fixed grading, `compactExp`,
`CompactCenter`, `NormalizerCenter`, and `UnitaryRepresentation`. No new
library, axiom, integration theory or root-datum/topology correspondence.

### Checked Results

**The finite center/quotient package is complete.**
[CenterThree](../../../../../Math/LieGroups/E6/Minuscule/CenterThree.lean) constructs
`centerThirdDirection` in the actual real matrix algebra. Its diagonal is
`grade(a) * 2*pi*I/3`, with each grade equal to `1`, `-2` or `4`.
`exp_centerThirdDirection` identifies its matrix exponential with
`scalarRoot3 * identity`. `centralScalar3 = compactExp centerThirdDirection`
therefore belongs to the existing identity component, without assuming
that arbitrary scalar roots belong to that component.

The checked results include:

- `centralScalar3_mem_center`, `centralScalar3_orderOf`: centrality and
  exact order three, using the primitive complex cube root.
- `compactCenter_card_bounds`: `3 divides |Z|` and `|Z| divides 27` for
  the same already constructed candidate center.
- `centralScalar3_val`, `centralScalar27_pow_nine_mem`: the ninth power
  of the known full-normalizer element of order 27 is this component
  element. Membership of the order-27 element itself is still unproved.
- [CentralQuotientObstruction](../../../../../GUT/E6/Minuscule/CentralQuotientObstruction.lean)
  proves that the actual Hilbert-27 action is `scalarRoot3` times the
  identity on this element, with character `27 * scalarRoot3`.
  `representation_not_descends_center` rules out factoring the actual
  representation through the quotient by the candidate's center.
  `compactCandidate_not_equiv_centerless` also excludes an abstract group
  isomorphism to any group whose center is proved trivial.

These statements concern the actual candidate and its actual quotient;
they do not supply an independently named adjoint E6 carrier or identify
that quotient with one. A nontrivial center is not a proof of simple
connectedness, and the divisibility bounds alone permit order nine or 27.
The subsequent [cubic package](E6_CUBIC_CENTER.md) separately excludes
these possibilities and proves the exact order-three center. The current
package's original bounds and audit remain valid.

## 6. Scope and limitations

### Global Boundary and Stop

The consumer is the global-form ledger: rule out a trivial candidate center
and rule out descent of the actual source to its center quotient. This is
one input to a possible global identification, not a sufficient criterion.
Even `3 divides |Z| divides 27` does not compute the exact center or prove
simple connectedness. No inference of that kind is permitted.

The still-missing global bridge is an actual compact-group/root-lattice or
covering/classification theorem connecting this carrier to the intended
simply connected E6. The earlier pinned-source finding remains unchanged.
Do not automatically proceed from this package into a cubic invariant,
exact-center or universal-cover project. Stop after the listed results,
or record a concrete failed equation without changing the carrier.

## 7. Sources and verification

### Verification and Exit

```sh
lake build GUT.E6.Audit.AuditCenterThree
lake build
```

The [persistent audit](../../../../../GUT/E6/Audit/AuditCenterThree.lean) checks 25
declarations against `propext`, `Classical.choice`, `Quot.sound`: 4358 jobs.
It retains the full-normalizer negative control, tests the actual quotient
statement, and exhibits `3 divides 9 divides 27` to prevent treating the
bounds as an exact-center theorem. The full regression is recorded in
[historical milestone record](../../../../topics/e6-global-topology/checkpoints/e6-topology.md). No new library or trusted external
calculation is used.

The finite deliverable is closed, **not the global identification**. The
remaining gap is a group-level topology/classification comparison, not a
missing finite matrix equality. A root-lattice route must first identify
an actual maximal torus (now completed by the later
[torus package](E6_COMPACT_TORUS.md)) and then connect its geometric coroot
data to the group's fundamental group; an alternative covering route must construct a global
map and prove its kernel trivial. Neither bridge is supplied by the
current Lie-algebra equivalence, abstract root datum, center bounds or
non-descent theorem. This package stops without opening those foundations
or starting the separate cubic-invariant route.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
