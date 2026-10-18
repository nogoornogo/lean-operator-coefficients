# E6 Torus Surjectivity: Literature-to-Lean Map

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../proof/README.md).

See the [proof-document conventions](../../../proof/TEMPLATE.md) for citation roles and build prerequisites.

External reference roles and the stage 04 bibliographic checks are recorded
in the [individual reference review](../../../proof/REFERENCE_REVIEW.md).

## 1. Result and status

**Policy update, stage 03:** the user approved an
[explicit literature-input boundary](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md) instead of
formalizing this full route. The older no-external-input restrictions below
describe the previous plan. R1-R7 are not activated tasks or accepted axioms.

Updated: stage 02

### Status And Bound

**Correspondence study complete; the full route is not an execution queue.**
The user requested this table before discussing further work. On stage 02,
the user requested a separately isolated local-prover plan. That packet supplied
a small pilot and review gates but has since been
[retired](../checkpoints/retired-e6-delegation.md). No local inference or proof
implementation was started in preparing it. This table remains the technical map, not approval
to implement every prerequisite recursively. E6-0 stays closed as an audit.
No Lean source, hypothesis, dependency or theorem status changes.

The endpoint remains exactly:

```text
Function.Surjective GUT.E6.Minuscule.Torus.fundamentalMap
```

Its consumer is the candidate's simple connectedness, not the already
checked physical theorem. Named global E6 identification remains unclosed.
References are proof guides, not new axioms or supplied certificates.

## 2. Inputs and conclusion

### Checked Inputs

Write `G = compactIdentityComponent`, `T = Torus.subgroup`, `B = G/T`.
`B` is a coset space, not a quotient **group**; no normality is assumed.
`fundamentalMap` instead starts from `Torus.Point = (Fin 6 -> Circle)`.
A future quotient proof must identify its map through the homeomorphism
onto the range of `Torus.hom`.

| Existing input | Project evidence | Boundary |
| --- | --- | --- |
| Actual compact connected Lie group | `MatrixLieGroupNormalizer` instances in [MatrixLieGroupComponent](../../../../Math/LieGroups/Matrix/MatrixLieGroupComponent.lean); `compactIsManifold` in [CompactAtlas](../../../../Math/LieGroups/E6/Minuscule/CompactAtlas.lean); `compactLieGroup` in [CompactLieGroup](../../../../Math/LieGroups/E6/Minuscule/CompactLieGroup.lean) | Not yet simple connectedness. |
| Closed six-circle inclusion and maximality | `hom_closedEmbedding`, `hom_phase` in [CompactTorus](../../../../Math/LieGroups/E6/Minuscule/CompactTorus.lean); `centralizer_eq`, `maximal_abelian` in [TorusCentralizer](../../../../Math/LieGroups/E6/Minuscule/TorusCentralizer.lean) | Not general torus conjugacy. |
| Actual tangent algebra and Cartan directions | `compactTangentRealFormLieEquiv` in [CompactLieAlgebra](../../../../Math/LieGroups/E6/Minuscule/CompactLieAlgebra.lean); `Torus.direction_matrix` | Not smooth quotient geometry or a global regular-locus theorem. |
| All torus loops contract in the candidate | `loopImage_nullhomotopic` in [TorusLoopContraction](../../../../Math/LieGroups/E6/Minuscule/TorusLoopContraction.lean); `fundamentalMap_trivial` in [TorusFundamentalGroup](../../../../Math/LieGroups/E6/Minuscule/TorusFundamentalGroup.lean) | Not surjectivity. |

## 4. Proof structure

### Correspondence Table

**API** means a library declaration was inspected, not that its candidate
application was compiled. **OPEN** means no completed candidate bridge was
found in the inspected sources. **ASSEMBLY** is also unproved; its named
inputs must first be closed. Rows are obligations, not an approved queue.
`Greg` and `Treg` denote proposed regular loci, not project declarations.

| ID | Required output / literature role | Available Lean input | Remaining work |
| --- | --- | --- | --- |
| R0 | Path connectedness of `G` and `B` | S1; checked atlas and connectedness | API / ASSEMBLY: register local path connectedness, then pass to the coset image. |
| R1 | Homogeneous-space infrastructure | S2; actual torus and tangent data | OPEN: smooth torus inclusion, actual charts/local sections for `B` and root-centralizer quotients. |
| R2 | Regular-locus inputs to Proposition 32 and Lemma 8 | Concrete Cartan/root data | OPEN: global torus conjugacy/coverage, open regular locus, nonempty `Treg`, and comparison with nonvanishing root-character factors. |
| R3 | Proposition 32 | R1-R2 and root data | OPEN: closed singular locus covered by actual smooth compact parameter spaces of dimension at most `dim G - 3`. Prove the derivative/dimension comparisons. |
| R4 | Lemma 7, restricted to injectivity on `pi1` | S3 | OPEN: relative deformation of disk/square maps avoiding the singular image, with boundary control. Image nullity alone is insufficient. |
| R5 | Lemma 8, covering property only | S4 | OPEN geometry / API topology: construct `q : B x T -> G`, `q(gT,t) = g*t*g^-1`; prove continuity, local homeomorphism over `Greg`, and restricted-domain comparison with `B x Treg`. |
| R6 | Proposition 37 | S5; R0-R2, R4-R5 | ASSEMBLY: product section, covering injection, homotopy and basepoint transport yield trivial `pi1(B)`; add path connectedness. |
| R7 | Proposition 38, surjectivity only | S6; R1, R6 | OPEN: actual quotient bundle and low-degree homotopy exactness, or a direct global homotopy lift with controlled boundaries. |
| R8 | Project endpoint and consumer | S7; checked triviality | ASSEMBLY: identify R7's map with `fundamentalMap`; infer trivial `pi1(G)` and combine with R0. |

Dependency skeleton:

```text
checked inputs -> R1, R2 -> R3 -> R4 ----+
                    |                  |
                    +-------> R5 ------+--> R6
R1 + actual bundle / low-degree lifting + R6 -> R7
R7 + Point-to-range transport -> target surjectivity
target + checked map triviality + R0 -> simple connectedness
```

Do not convert R1-R5 or R7 into assumptions of a new E6 theorem. Proving
R6 conditionally would not close these candidate source obligations.

### Inspected Lean Interfaces

Paths are relative to package roots under `.lake/packages/`. Historical audit pins: Lean
`4.34.0-rc2`; mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`;
TauCeti `355c248fa848acd70c2a4b412ca5f53d37b0402a`.

| Key | Source and reusable declarations | Limitation |
| --- | --- | --- |
| S1 | Mathlib `Geometry/Manifold/ChartedSpace.lean`: `ChartedSpace.locallyPathConnectedSpace`; `Topology/Connected/LocallyPathConnected.lean`: `PathConnectedSpace.of_locallyPathConnectedSpace`; `Topology/Connected/PathConnected.lean`: `Function.Surjective.pathConnectedSpace` | No inference that `Greg` or a fiber is connected just because `G` is. |
| S2 | Mathlib `Topology/Algebra/Group/Quotient.lean`: `QuotientGroup.continuous_mk`, `isOpenQuotientMap_mk`, quotient compactness; `Geometry/Manifold/Instances/Quotient.lean`: `MulAction.instChartedSpaceQuotient` | The latter requires a free properly discontinuous action, not a positive-dimensional torus action. |
| S3 | TauCeti `Analysis/Calculus/Sard/LowDimension.lean`: `Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank`; Mathlib Hausdorff-dimension API | Not relative smooth approximation or disk avoidance on manifolds. The inspected TauCeti `Analysis/Fredholm/SardSmale.lean` also does not instantiate that deformation. |
| S4 | Mathlib `Topology/Covering/Basic.lean`: `IsCoveringMapOn.of_isLocalHomeomorphOn`, `IsCoveringMapOn.isCoveringMap_restrictPreimage` | Needs an actual continuous map, compact Hausdorff source, Hausdorff target, and local-homeomorphism proof over the locus. |
| S5 | Mathlib `Topology/Homotopy/Lifting.lean`: `IsCoveringMap.injective_path_homotopic_map`; `AlgebraicTopology/FundamentalGroupoid/InducedMaps.lean`: `Path.Homotopic.map_trans_evalAt`; `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`: `FundamentalGroup.fundamentalGroupMulEquivOfPath` | Does not construct the actual covering or homotopy. |
| S6 | Mathlib `Topology/FiberBundle/Trivialization.lean`: `Bundle.Trivialization.liftCM`, `clift`, `proj_clift` | Local lifts within one trivialization, not global relative lifting or exactness for `G -> B`. No ready-to-use instance of that bundle-level result was found. |
| S7 | Mathlib `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`: `FundamentalGroup.mapOfEq`; `AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`: `simply_connected_iff_loops_nullhomotopic` | Candidate casts, domain equivalence and all-basepoint transport still need checking. |

This is bounded source inspection, not a proof of absence from every
library. No new candidate instantiation was compiled in this study.

### Reductions And Guardrails

These are implementation judgments, not newly checked theorems:

- **No covering-degree calculation:** S4 can start with the full compact
  source `B x T`, establish a covering on `Greg`, then restrict preimages.
  Do not assume `B x Treg` itself is compact. Exact Weyl-group order is not
  a necessary output for our consumer.
- **No higher homotopy calculation:** omit Proposition 36 and the `pi2`
  part of Lemma 7. R6 uses injectivity, not an assertion that a covering
  always induces an isomorphism on fundamental groups.
- **No chamber/component computation:** select a regular `p`; the section
  `b -> (b,p)` has projection as a retraction. No contractibility of a
  component of `Treg` is assumed.
- **Moving basepoints:** along a path `a` from `p` to `1` in `T`, the
  proposed homotopy `H(s,gT) = g*a(s)*g^-1` has basepoint trace `a(s)`.
  It need not stay in `Greg` and is not based at a fixed regular point.
  Use S5's transport; never use `1` as a regular point for this candidate.
- **Only low-degree bundle exactness:** R7 need not implement a general
  long exact sequence. A direct proof still needs global lifting and
  boundary control; discrete-cover lifting cannot replace it.
- **Preserve existing contractions:** no full coroot-lattice kernel
  classification is needed after the checked `fundamentalMap_trivial`.

## 6. Scope and limitations

### Assessment For Discussion

Literature fixes the mathematical route, and S4/S5 reduce its outputs.
It does **not** make this a small adapter between existing declarations.
Three substantial work areas remain:

1. **Actual homogeneous geometry:** R1-R3 and R5's local geometry, including
   global conjugacy. Algebraic exponential generation is not a substitute.
2. **Relative avoidance:** R4, beyond Sard's measure-zero conclusion.
3. **Quotient-bundle lifting:** R7, beyond discrete-cover theory.

This is an inventory, not three short milestones or a time estimate.
Costs have not been measured. R6/R8 are plausible smaller assembly steps
only after these inputs; the earlier rows can require substantial foundations.

**Recommendation:** do not launch the full route as another bounded
continuation. Discuss whether implementation of these specific known
theorems is acceptable, or preserve the candidate result and defer global
identification until suitable foundations are available. If substantial
foundational implementation must be avoided, this route does not presently
meet that requirement. No next proof task is activated.

## 7. Sources and verification

The versions and build counts below belong to this audit checkpoint. For the
current checked source, use the [baseline entry point](../../proof-program-context/interface-checkpoint.md#checked-baseline).

### Sources

**R:** M. S. Raghunathan lectures, *Compact Lie groups and their
representations*, 56-page PDF, accessed stage 01:
[Proposition 32](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=34),
[Lemmas 7-8](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=36),
[Propositions 37-38](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=37).
Anchors use PDF page numbers. The first-page note identifies Akash as the
typist and says the lecturer has not yet proofread the notes. Lemma 8 is
stated without proof there; the kernel part of Proposition 38 proves only
one inclusion. Do not treat the full classification as an expanded script.

**C:** Brian Conrad,
[Size of fundamental group, Section 3](https://math.stanford.edu/~conrad/210CPage/handouts/pi1size.pdf#page=4),
clarifies the same route: Proposition 3.1/Lemma 3.2 give the regular
covering argument; Lemma 3.3/Corollary 3.4 discuss the singular locus and
its complement. This is not a second implementation route. The deformation
argument still invokes background smooth topology.

**Source spine:** R's Proposition 32 controls the singular locus. Lemma 7
compares fundamental groups after removing it; Lemma 8 supplies a regular
conjugation covering. Proposition 37 combines injectivity with a homotopy
to a constant map. Proposition 38 uses the quotient fibration for
surjectivity. Its remaining kernel calculation is unnecessary here.
[R, PDF pages 34-38](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=34)

Below is our implementation assessment, not new Lean-checked mathematics.

### Verification And Exit

The requested artifact is this table, its references and its unresolved
interfaces. Only documentation changes; local file links and
`git diff --check` are checked. No Lean build or axiom audit is rerun.
The last full proof baseline remains `checkpoint 01` (5505 jobs / 2607 reports);
the subsequent torus-audit rerun is recorded in
[historical milestone record](../checkpoints/e6-topology.md).

All proofs, dependency pins and physical scope are preserved. Stop for the
requested discussion, rather than implementing R1 or R4 automatically.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
