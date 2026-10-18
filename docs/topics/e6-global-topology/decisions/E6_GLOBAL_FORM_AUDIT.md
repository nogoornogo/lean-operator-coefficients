# E6 Global Form Audit

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../proof/README.md).

See the [proof-document conventions](../../../proof/TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

**stage 03 update:** see [the literature boundary](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).
Simple connectedness now has a checked implication from an explicit external
topology input. Named-E6 interpretation also uses external classification;
unconditional Lean global identification remains open. The audit below is historical.

Updated: stage 02

### Result

**This audit is closed.** After the actual-model milestone `checkpoint 01`, the
user requested further global-form work. A separately bounded
[order-three center/quotient package](../../../proof/current/inputs/Math/E6_CENTER_THREE.md) now proves the
central Cartan exponential and non-descent of the actual 27 to the center
quotient. The subsequent bounded [cubic package](../../../proof/current/inputs/Math/E6_CUBIC_CENTER.md) proves
the exact order-three center. The later [coroot-loop package](../../../proof/current/inputs/Math/E6_COROOT_LOOPS.md)
contracts each of the six actual Cartan coordinate loops in the candidate.
The [all-torus-loop package](../../../proof/current/inputs/Math/E6_TORUS_LOOPS.md) extends this to every
identity-based torus loop and proves the induced fundamental-group map trivial.
Simple connectedness/global identification
remain unproved and deferred. The remaining route below is research context, not an
automatic next-task authorization; follow the
[endpoint-first plan](../plans/E6_ENDPOINT_PLAN.md).

**E6-0o is complete as a source/feasibility audit, not a global-form proof.**
The [geometric Lie-algebra identification](../../../proof/current/inputs/Math/E6_TANGENT_LIE_ALGEBRA.md) is
checked. No direct theorem identifying this connected compact matrix group
as simply connected E6 was found in the pinned sources inspected below.
No dependency change or general integration project is authorized by this
checkpoint. The existing foundations cost gate remains in force.

## 4. Proof structure

### Deferred Construction Route

The audit proposed the following route. Items 1-3 are now completed;
item 4 is deferred and is not required to finish the feasibility audit:

1. **E6-0p: scalar-center upper bound, completed.** Differentiate the equality between
   a central element and every real-form exponential. Extend commutation
   from the real form to its complexification, then reuse the checked scalar
   commutant. The SU(27) determinant condition bounds the scalar by
   `z^27 = 1`. This does not prove that every such scalar lies in the component.
2. **Order-three lower bound, completed separately.** The actual Cartan
   exponential is a primitive cube-root scalar in the identity component;
   no root-datum/group correspondence is assumed. The actual 27 acts
   nontrivially on it and does not descend to the center quotient. This
   narrows the global-form possibilities but does not establish item 4.
3. **Exact center, completed separately.** The [cubic package](../../../proof/current/inputs/Math/E6_CUBIC_CENTER.md)
   constructs a nonzero degree-three function, checks infinitesimal
   invariance against all 78 actual basis matrices, and proves invariance
   under generated exponentials. Its scalar action imposes `z^3 = 1` and
   gives the center isomorphism to cube roots. Neither the scalar upper
   bound nor the Albert algebra's dimension count alone supplied this bridge.
4. **Simple connectedness remains separate even from an exact center.** The
   subsequent [torus package](../../../proof/current/inputs/Math/E6_COMPACT_TORUS.md) constructs an actual
   closed six-circle subgroup, exact Cartan period lattice and self-centralizer.
   The subsequent [coroot-loop package](../../../proof/current/inputs/Math/E6_COROOT_LOOPS.md) constructs
   actual based contractions of its six coordinate loops. The later
   [all-torus-loop package](../../../proof/current/inputs/Math/E6_TORUS_LOOPS.md) proves triviality of the
   entire induced fundamental-group map using actual covering lifts.
   Surjectivity from the torus fundamental group to that of the candidate
   remains open, as does an alternative classification/covering theorem. Neither these results
   nor matching Lie algebra and center orders prove simple connectedness.

The full normalizer's primitive order-27 scalar is now proved **outside**
the identity component, whereas its ninth power has proved membership.
The distinct centers are consistent with the existing local E6 result.

### Torus Surjectivity Follow-Up

**Decision (stage 01, after `checkpoint 02`): deferred at the foundations gate.**
The user's continuation request prompted one bounded inspection of the two
routes below, using the pinned sources only. Neither supplied an end-to-end
proof package within the existing interfaces. This is a source-audit result,
not a mathematical impossibility result or a proof of surjectivity.

The frozen target was exactly
`Function.Surjective GUT.E6.Minuscule.Torus.fundamentalMap`, with no new
hypotheses on the actual candidate. Its consumer is the candidate's global
simple-connectedness obligation, not the already proved physical theorem.
Since `fundamentalMap_trivial` is proved, this target is equivalent to
triviality of the candidate's fundamental group at the identity. Repackaging
surjectivity as an assumed certificate would leave that entire input open.

| Inspected route | Available source | First unavailable interface and downstream obligations |
| --- | --- | --- |
| Flag quotient `K/T` | Mathlib `Topology/FiberBundle/Trivialization.lean`: `Bundle.Trivialization.liftCM`, `clift`, `proj_clift`; TauCeti `GroupTheory/TitsSystem/Bruhat/Basic.lean`: `TitsSystem.bruhatCells_eq_univ` | No actual flag-space presentation of this `K/T` with proved simple connectedness was found. This route also needs the actual quotient bundle and sufficient global homotopy lifting to derive surjectivity. Local lifts in one trivialization and abstract double-coset coverage do not provide those comparisons. |
| Universal cover | TauCeti `AlgebraicTopology/UniversalCover/Covering.lean`: `UniversalCover.isCoveringMap`, `simplyConnectedSpace`, `existsUnique_continuousMap_lifts` | The APIs concern a cover of a space satisfying local hypotheses; they do not compute this candidate's covering fiber. A compatible covering-group/Lie structure and a global kernel or torus-preimage argument would still have to be supplied. Simple connectedness of the cover is not simple connectedness of its base. |

Search scope included the pinned Lie/exponential and Riemannian-geodesic
modules, fundamental-group and universal-cover modules, fiber-bundle and
homotopy-lifting modules, and the algebraic torus/Bruhat interfaces. No
ready-to-apply compact-Lie maximal-torus fundamental-group surjectivity
theorem was found in that inspection. In particular:

- TauCeti `Algebra/AlgebraicGroup/Torus/Maximal.lean` defines maximality in
  Hopf coordinates and transport; it explicitly leaves existence/conjugacy
  open. It is not a theorem about this compact topological subgroup.
- The inspected Lie exponential and geodesic modules provide local tools,
  not a completed global loop-reduction theorem for this carrier.
- Mathlib's covering homotopy-lifting theorem cannot be applied to `K -> K/T`
  merely because it applies to discrete-fiber covers.
- The existing algebraic exponential-generation theorem supplies products
  of elements, not continuously chosen factorizations of arbitrary loops.

**Exit:** no new Lean theorem or endpoint input is closed. Preserve the
checked contractions; do not start another matrix-computation package or
implement prerequisites recursively. Resuming either route requires an
explicitly approved foundational project with the actual surjectivity
endpoint and a reviewed list of missing geometric interfaces. No reliable
small-patch estimate follows from the fact that the target has one line.
This inspection does not rule out a future direct argument or a useful
library addition; neither is available as a checked bridge at this checkpoint.

Verification: reran `lake build Math.LieGroups.E6.Audit.AuditTorusLoops` successfully
(3921 jobs, including cached replay; 26 standard-axiom reports). No Lean
source or dependency changed; the full build was not rerun. The last full
baseline remains `checkpoint 02`: 5505 jobs / 2607 reports. This documentation
checkpoint does not reopen E6-0 or change any physical conclusion.

The later user-requested
[Raghunathan 37/38 correspondence study](E6_TORUS_SURJECTIVITY_MAP.md)
now maps this route to exact pinned APIs and missing geometric interfaces.
It identifies avoidable covering-degree/higher-homotopy calculations but
does not close surjectivity or authorize foundation implementation.
At that checkpoint the next action was policy discussion, not another
automatic proof package. The stage 02 local-prover packet prepared an isolated
pilot with independent review; it has since been
[retired](../checkpoints/retired-e6-delegation.md). It did not close the blockers
above or authorize the entire foundational route. Current treatment uses the
[explicit literature boundary](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).

## 6. Scope and limitations

### Cost Gate

These estimates record the original proposal, not a renewed implementation
budget. No deferred task is resumed automatically based on its estimate.

Planning judgments, not measured times or credit guarantees:

- Scalar-center upper bound: one bounded proof checkpoint, provisionally
  1-2 workdays; derivative and commutant APIs already exist locally.
- Concrete order-three scalar: provisionally 1-3 workdays for a preflight;
  reassess if explicit exponential/lattice transport becomes substantial.
- Cubic invariant and exact center: estimate only after inspecting a finite
  invariant certificate and the exponential-action bridge. The finite
  computation alone does not close the group statement.
- Simply connected global identification and general integration: retain
  the separate weeks-to-months review gate. No reliable end-to-end bound.

The shared physical selection-rule theorem only needs an actual compatible
SU(5) homomorphism into the ambient group, not simple connectedness by
itself. The direct SU(5) inclusion and positive-target 27 inhabitant are now
checked on the candidate. Naming the endpoint as the intended global compact
E6 and the optional Spin intermediate inclusion remain unclosed obligations.
These must not be hidden in a supplied certificate.

## 7. Sources and verification

The versions and build counts below belong to this audit checkpoint. For the
current checked source, use the [baseline entry point](../../proof-program-context/interface-checkpoint.md#checked-baseline).

### Pinned Sources

This historical audit used Lean 4.34.0-rc2, mathlib
`30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, and TauCeti
`355c248fa848acd70c2a4b412ca5f53d37b0402a`.

| Source | Available result | Missing bridge |
| --- | --- | --- |
| TauCeti `Geometry/Lie/Functor.lean` | Differentiate an existing smooth homomorphism to a Lie homomorphism; already reused | Integration of a Lie homomorphism to a global group homomorphism |
| TauCeti `Geometry/Lie/Exponential/` | Exponentials, one-parameter subgroups, local inverse results | Global simply connected integration/classification |
| TauCeti `AlgebraicTopology/UniversalCover/` | Based-path construction, covering and simple connectedness under local hypotheses | Compute this candidate's covering kernel; prove it trivial, or identify the cover and its faithful 27 action |
| TauCeti `AlgebraicGeometry/AffineGroupScheme/SimplyConnected.lean` | Scheme-level definition via central isogenies, transport and kernel-free criteria | A proof for the actual minuscule carrier; comparison with compact real-group topology |
| TauCeti `Algebra/Lie/E6/Minuscule/{GroupScheme,RootDatum,Frobenius}.lean` | Explicit carrier, weight torus, root subgroup characters and abstract root-datum comparison | Files explicitly leave reductivity, maximality and global simply connected identification unproved |
| TauCeti `RepresentationTheory/Compact/Integrated.lean` | Haar-integrated operators of an existing representation | Not integration of Lie-algebra representations |
| TauCeti `Algebra/AlbertAlgebra.lean` | Split 27-dimensional algebra and elementary operations | No identified cubic-invariant stabilizer comparison to these minuscule matrices |

Searches of pinned mathlib/TauCeti Lie, topology and algebra directories for
Lie second/third theorems, Lie-homomorphism integration and compact Lie-group
classification found no direct bridge. This is a bounded source audit, not
a claim that no alternative proof exists. Roadmap targets and abstract
definitions are not counted as implemented results.

### Verification Boundary

The original E6-0o checkpoint changed documentation only. Its verified baseline was
E6-0n: full build **5468 jobs / 2370 axiom reports**, all using only
`propext`, `Classical.choice`, `Quot.sound`; ten tooling tests pass.
No new Lean theorem, physical assumption or physical endpoint was claimed
by that audit. Later proof/build records are in [historical milestone record](../checkpoints/e6-geometry.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
