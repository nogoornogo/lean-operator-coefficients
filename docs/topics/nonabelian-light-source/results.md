# Finite Non-Abelian Light Coefficients

## Checked Endpoint

`GUT.NonabelianLightOperators.both_coefficients_exist` constructs nonzero
H-equivariant linear maps from the ordered tensor products of actual light
weight spaces to the trivial complex representation:

```text
(Q_0 tensor Q_3) tensor (u_8* tensor e_14*) -> C
(d_9* tensor u_8*) tensor (Q_2 tensor L_13) -> C
```

Subscripts refer to the existing fifteen SM weights, not generations. The
two chosen weight combinations sum to zero, checked by `qque_slots_neutral`
and `duql_slots_neutral`. The starred spaces are contragredients of the
left-chiral sectors. The more general coefficient theorems permit any
corresponding species weights; only the displayed slots assert torus neutrality.

`not_forbidsBothInternalCoefficients` rules out vanishing of both residual
coefficient spaces. The qque theorem needs a nonzero Q target only; obtaining
both displayed coefficients additionally requires a nonzero down target.

## Exact Inputs

1. An arbitrary ambient group G, a torus homomorphism j, and the same three
   actual ambient conjugations used by the structural criterion.
2. A finite ordinary residual group H, **not assumed Abelian**, acting through
   an actual finite-dimensional complex representation of G x H. Product-group
   action expresses strict commutation. Only the torus restriction is required
   to be unitary by this theorem; no finite-group classification is an input.
3. An invariant symmetric bilinear mass on the restricted torus x H action.
   Light fields are its actual radical. Conjugators need not preserve this mass.
4. Five finite-dimensional actual H representations as positive local targets,
   one per SM species. At each of the fifteen weights, the light character
   minus the opposite-weight dual character equals the corresponding target
   character. Nothing is prescribed at other weights.
5. Nonzero Q/down targets independently. Their dimensions need not agree.

Cross-species character equalities and common irreducible constituents are
derived, not hypothesized. Surjective projections are split using Maschke;
dualizing their inclusions gives the required surjections on starred fields.
Tensor evaluation is nonzero by surjectivity, including after the explicit
factor permutations. No `sorry`, new axiom, assumed nonzero channel, or assumed
light projection certificate is used.

## Abelian Consistency

`NonabelianAbelianRecovery.matches_iff_matchesSM` proves equivalence with the
old coefficientwise local target, on the common domain of actual unitary
Abelian light/target representations. It uses full joint eigenspaces, not a
chosen basis or the dimension of a complete multiplet. `actualSpectrum_radical`
identifies its spectrum with the existing restricted mass-source spectrum.
`speciesProfile_positive_iff` identifies nonzero targets with positive old
charge-profile totals. This recovery does not need H finite.

This is a consistency equivalence for profiles extracted from actual unitary
targets, not a new classification of arbitrary abstract charge-label systems.
The old Abelian theorem, including infinite Abelian groups, remains intact;
the new constituent-extraction theorem requires finite H. Neither theorem
supersedes the other on every input domain.

## Scope And Stop Gate

The approved endpoint is reached: an ordered **residual internal coefficient**
on actual light sectors. A torus-neutral coefficient is not automatically an
invariant of the full SM gauge group. A fully gauge-equivariant lift for an
arbitrary mass radical, antisymmetrization/Lorentz nonvanishing, generated
Wilson coefficients, amplitudes and lifetimes are not proved. No such missing
bridge is silently supplied by the earlier concrete SU(5)/SU(6) tensor examples.

Finite S3/A4 controls from the [earlier bounded audit](../nonabelian-invariant-audit/finite-controls.md)
remain controls, not complete phenomenological source models. Compact infinite
non-Abelian H, nonstandard SM embeddings, R symmetries, generalized symmetries
and the E6 global-form literature input are unchanged boundaries. No conclusion
that every GUT must cause proton decay follows.

The retained topic branch is `proof/nonabelian-light-source`. After the final
checkpoint, the user approved master integration, lifting the previous hold.
Git ancestry records integration. Further research needs a new bounded topic,
not an unbounded continuation of this completed bridge.

## Verification

Final checkpoint, stage 01:

- Four focused final audit targets: 3847 jobs, 23 strict declaration checks.
- Full `lake build`: 5609 jobs passed, including the earlier source audits.
- `node tools/layout/check-layout.mjs`: 588 modules; layers, cycles and aggregates passed.
- `node tools/docs/check-links.mjs`: 239 Markdown files, 1286 local links,
  32 heading fragments, zero errors.
- `git diff --check`: passed. No dependency/toolchain changes, merge or push.

The preceding source milestone `checkpoint 01` added 11 strict checks; the earlier
NS-1 checkpoint `checkpoint 02` added 17. All remain registered and pass together.

See the strict audits registered in `Math.lean` and `Physics.lean`. They admit
only `propext`, `Classical.choice` and `Quot.sound` transitively and check the
Math/Physics/GUT import layers. Dependency pins are unchanged.

The actual qque/duql applications require local finite heartbeat allowances
for nested radical/weight-space type checking; no global limits or audit
allowlists were relaxed. Their focused build took about 78 seconds on this
checkout. Other new modules build without warnings; old warnings are replayed.
