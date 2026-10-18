# All Torus Loops in the E6 Candidate

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Construction

- [CircleLoopLift](../../../../../Math/Topology/CircleLoopLift.lean) constructs a
  continuous angle lift starting at zero. `exp_angle` proves that it lifts
  the original loop, not a replacement path. The circle exponential's
  exact period theorem gives `angle_one_period`. Dividing by `2*pi` gives
  `turns`, with initial value zero and integral final value. No sign or
  size bound is imposed on that integer.
- [TorusLoopContraction](../../../../../Math/LieGroups/E6/Minuscule/TorusLoopContraction.lean)
  derives `hLine_int_mul` from the actual one-parameter group law. This
  extends `Coroot.filling` to all integer endpoints (`filling_integer`).
  `loopFilling` is the ordered product of six fillings, each evaluated on
  the normalized lift of the corresponding input coordinate. Intermediate
  factors are not assumed to commute. `hom_coordinate_product` identifies
  the initial path with the actual inclusion; the final path and both
  fixed boundaries are proved separately. `loopContraction` bundles an
  actual based homotopy for every `p : Path (1 : Torus.Point) 1`.
- [TorusFundamentalGroup](../../../../../Math/LieGroups/E6/Minuscule/TorusFundamentalGroup.lean)
  defines the induced homomorphism with mathlib's `FundamentalGroup.mapOfEq`.
  `fundamentalMap_loop` compares its action with `loopImage` including the
  basepoint casts. Quotient induction and the actual contractions prove
  `fundamentalMap_trivial` and `fundamentalMap_range` (range is bottom).

The [persistent audit](../../../../../Math/LieGroups/E6/Audit/AuditTorusLoops.lean) checks
26 declarations against `propext`, `Classical.choice`, `Quot.sound`.
It verifies fixed endpoints, negative and large integer windings, arbitrary
six-tuples of mixed windings, and that the original group inclusion is
nontrivial even though its induced fundamental-group map is trivial.

```sh
lake build Math.LieGroups.E6.Audit.AuditTorusLoops
lake build
```

Targeted: **3921 jobs / 26 reports**. Full: **5505 jobs / 2607 reports**
(2606 lists and one axiom-free report). New modules are warning-free.
Dependency pins and physical hypotheses/endpoints are unchanged.

**Stop gate reached:** all three interfaces are closed. The proof concerns
loops contracting in the candidate, not in the torus itself. It does not
assert that the inclusion of the entire torus is null-homotopic as a map
of spaces, or that the candidate is simply connected.

## 2. Inputs and conclusion

### Frozen Endpoint

**LEAN-CHECKED:** every identity-based loop in the actual six-circle torus maps
to an endpoint-fixed null-homotopic loop in `compactIdentityComponent`.
Consequently its inclusion induces the trivial homomorphism on fundamental
groups. This bounded continuation follows `checkpoint 01` and closes the first
remaining interface in [the coroot-loop package](E6_COROOT_LOOPS.md).

The candidate's simple connectedness is not an input or conclusion.
Proving that every candidate loop comes from a torus loop is a separate
surjectivity theorem, not a consequence of this package.

### Interfaces And Bound

1. Use mathlib's `Circle.isCoveringMap_exp` and `IsCoveringMap.liftPath`
   to construct continuous real lifts of arbitrary circle loops, starting
   at zero and ending at an integral multiple of `2*pi`.
2. Extend the existing actual coroot filling to every integer endpoint,
   including negative winding, and multiply the six coordinate fillings
   in a fixed order. Identify the starting path with the actual torus
   inclusion. All intermediate values must remain actual group elements.
3. Bundle the null-homotopy and prove the induced fundamental-group
   homomorphism equals the trivial one. Add persistent audit controls.

The pinned TauCeti circle/product fundamental-group calculations are
available, but explicit covering lifts give a shorter route here: the
previous filling is already defined for all real path parameters. No
new winding classification or Lie integration foundation is required.

Allowed helpers are covering lifts, integer powers, finite products and
the existing homotopy/quotient APIs. No dependency upgrade, physical scope
change, global classification or new simply connected carrier is allowed.
If a new foundational prerequisite appears, record it and stop instead
of extending the plan recursively.

## 6. Scope and limitations

### Acceptance And Exit

Targeted audit, full `lake build`, standard axiom allowlist, link/diff
checks, documentation and thematic commit. Stop when the three interfaces
close. The outstanding surjectivity theorem remains separately scoped.

### Remaining Global Bridge

The missing statement on this route is now
`Function.Surjective Torus.fundamentalMap`: every identity-based candidate
loop class has a representative coming from the actual torus. It is not
proved by exponential generation or by this map's now-proved triviality.
Together with that surjectivity and path connectedness, the result would
give simple connectedness; the current theorem does not assume this step.
No new global foundation is automatically queued. See
[the owning topic](../../../../topics/e6-global-topology/README.md) and
[the historical global-form audit](../../../../topics/e6-global-topology/decisions/E6_GLOBAL_FORM_AUDIT.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
