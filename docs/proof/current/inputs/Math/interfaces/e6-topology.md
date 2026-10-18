# Actual E6 Candidate Topology

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Actual torus-loop images
contract and the induced fundamental-group map is trivial; candidate simple
connectedness is conditional.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

All names below concern `GUT.E6.Minuscule.compactIdentityComponent`, not
an assumed identification with the simply connected compact E6 group.

## 2. Inputs And Conclusion

The concrete carrier is `GUT.E6.Minuscule.compactIdentityComponent`. The
conditional endpoint takes an explicit maximal-torus surjectivity argument.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Coroot rotation fillings combine with lifted circle windings to contract all
torus loops; surjectivity, when supplied, gives the conditional conclusion.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Torus And Loops

| Module | Checked interface |
| --- | --- |
| `Math/LieGroups/E6/Minuscule/CompactTorus` | `Torus.hom`, closed embedding, exact Cartan exponential kernel |
| `Math/LieGroups/E6/Minuscule/TorusCentralizer` | `Torus.centralizer_eq`, maximality among Abelian subgroups |
| `Math/LieGroups/Matrix/RotationExponential` | `exp_eq_rotation` in real Banach algebras when `X^3 = -X` |
| `Math/LieGroups/E6/Minuscule/CorootRotations` | Actual matrix relations, `half_period_commutes`, `quarter_turn` |
| `Math/LieGroups/E6/Minuscule/CorootLoops` | Actual exponential lines, `hLine_torus`, `loop`, `contraction`, `loop_nullhomotopic` |
| `Math/LieGroups/E6/Audit/AuditCorootLoops` | 27-declaration axiom allowlist, both fixed boundaries, torus comparison, nonconstant midpoint |
| `Math/Topology/CircleLoopLift` | Actual circle-cover angle lifts, normalized `turns`, integral loop endpoint |
| `Math/LieGroups/E6/Minuscule/TorusLoopContraction` | Integer endpoint filling, ordered coordinate product, `loopContraction`, `loopImage_nullhomotopic` for every torus loop |
| `Math/LieGroups/E6/Minuscule/TorusFundamentalGroup` | `fundamentalMap_loop`, `fundamentalMap_trivial`, `fundamentalMap_range` |
| `Math/LieGroups/E6/Audit/AuditTorusLoops` | 26-declaration axiom allowlist, fixed boundaries, mixed integer windings, nontrivial group inclusion |

`Coroot.contraction` has type
`(Coroot.loop i).Homotopy (Path.refl 1)` for every `i : Fin 6`.
No simple-connectedness, loop-generation or Lie-integration assumption is
an input. All four factors of the filling are actual group elements.

`Torus.loopContraction` handles every identity-based torus loop. The
induced homomorphism `Torus.fundamentalMap` is now proved trivial, not just
on coordinate generators. Its unconditional surjectivity remains unformalized;
it is not inferred from the matrix or period certificates.

## 6. Scope And Limitations

Unconditional surjectivity and equivalence to an independently named global E6 carrier are not proved.

### Explicit Literature Boundary

The stage 01 user-approved route accepts maximal-torus surjectivity as an
external mathematical input, not a proved library theorem or a global axiom.

| Module | Interface |
| --- | --- |
| `Math/Topology/MaximalTorusFundamentalGroup` | `MaximalTorusData`, `MaximalTorusSurjectivityInput`, basepoint-transport consumer |
| `Math/LieGroups/E6/Minuscule/FundamentalGroupSurjectivity` | Actual `Torus.maximalTorusData`, exact map equality, `compactSimplyConnected_of_literature` |
| `Math/LieGroups/E6/Audit/AuditLiteratureTopology` | Actual hypotheses, conditional conclusion, preserved local results; strict 14-declaration audit |

The input is an explicit theorem argument; simple connectedness is not a global
instance. The mathematical named-E6 interpretation additionally uses external
Lie correspondence and compact-real-form classification, not a new Lean
equivalence. See [the literature ledger](../../GUT/E6_LITERATURE_BOUNDARY.md).
Rejected local-prover statements are archived, not used as hypotheses.

See [the torus dossier](../E6_COMPACT_TORUS.md) and
[the coroot-loop dossier](../E6_COROOT_LOOPS.md) and
[the all-torus-loop dossier](../E6_TORUS_LOOPS.md) for scope,
implementation and verified build records. The older chart, manifold and
tangent-algebra modules are unchanged by this package.

## 7. Sources And Verification

The [scope dossier](../../GUT/E6_LITERATURE_BOUNDARY.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

External theorem input: maximal-torus fundamental-group surjectivity
(Raghunathan Proposition 38) supplies an explicit Lean argument, not a global
axiom or a proved premise. The linked literature ledger records its conditions
and the separate named-group interpretation.
