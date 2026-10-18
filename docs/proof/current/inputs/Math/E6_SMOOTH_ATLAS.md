# E6 Candidate Smooth Atlas

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**E6-0k is complete.** The existing connected compact matrix candidate
has a `ChartedSpace` and `IsManifold` instance, modelled on the actual
78-dimensional real form. Its topology is unchanged. Charts and smooth
compatibility are constructed, not provided as assumptions.

[CompactAtlas](../../../../../Math/LieGroups/E6/Minuscule/CompactAtlas.lean) translates the
[identity chart](E6_LOCAL_CHART.md) by group multiplication. At `g`, the
chart is `h |-> log(g^-1 h)` on its proved source and its inverse is
`X |-> g exp(X)`. Every point belongs to its preferred chart's source,
and its coordinate is zero.

The transition from the chart at `g` to the chart at `h` is
`X |-> log(h^-1 g exp(X))`, with the same total extension of the logarithm
outside valid domains. On each overlap the argument lies in the checked
identity-chart target. The ambient logarithm is analytic there; matrix
multiplication and exponential are analytic. Thus every transition is
analytic on its source, and mathlib's `isManifold_of_contDiffOn` supplies
the smooth (`infinity`) manifold instance. No smooth-subgroup theorem or
new external tool is needed.

The ambient derivative of the parametrization `X |-> exp(X)` at zero is
proved to be the real-form inclusion as a continuous real-linear map
(`compactExp_hasStrictFDerivAt_zero`). This is not yet a comparison with
mathlib's tangent Lie bracket or a group integration theorem.

## 6. Scope and limitations

### Next Bounded Checkpoint

**[E6-0l](E6_CANDIDATE_LIE_GROUP.md) is now complete:** smooth matrix
inclusion and actual matrix operations give the `LieGroup` instance.
Subsequent [E6-0n](E6_TANGENT_LIE_ALGEBRA.md) also proves the differential
and geometric Lie-bracket comparison. Report any need for general
integration/classification foundations before expanding to global form.

The exact center, simple connectedness, global E6 identification, actual
compact Spin(10) inclusion and positive-target 27 model remain open.
There is still no new physical endpoint or change to physical assumptions.

## 7. Sources and verification

### Verification

[AuditCompactAtlas](../../../../../Math/LieGroups/E6/Audit/AuditCompactAtlas.lean), included in
`GUT.lean`, checks 14 new declarations with only `propext`,
`Classical.choice`, and `Quot.sound`. Concrete examples instantiate the
atlas, manifold, chart coverage and smooth transitions. The previous
periodic scalar negative control remains imported.

Targeted: **3863 jobs / 80 reports**, including 66 reused reports.
Full: **5447 jobs / 2336 reports** (2335 lists and one axiom-free report),
all standard axioms only. Both new modules and the extended chart module
are warning-free. Ten Python tooling tests pass.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactAtlas
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
