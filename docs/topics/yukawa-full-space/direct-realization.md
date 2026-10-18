# Direct Realization Of Five Mass Directions

Status: proved; bounded child milestone of the in-progress full-space topic.
Branch/integration target remain those in the [topic record](README.md).
Starting checkpoint: `checkpoint 01`. No merge while full-space completeness is open.

## Endpoint And Inputs

Keep the actual SU(6) representation, scalar, fixed vacuum and zero bare mass
unchanged. Prove that the five candidate mass directions can all be generated
by full-group invariant Yukawa couplings and are independent. Do not assume
the externally computed commutant, its dimension, or its vacuum image.

Sources:

- [Generic evaluation API](../../../Physics/FieldTheory/Yukawa/ProjectedYukawaEvaluation.lean)
- [Actual SU(6) construction](../../../GUT/SU6/Yukawa/FiveCouplings.lean)
- [Generic audit](../../../Physics/FieldTheory/Yukawa/Audit/AuditProjectedYukawaEvaluation.lean)
- [Model audit](../../../GUT/SU6/Audit/AuditFiveCouplings.lean)

No new web references were consulted. The construction uses the repository's
existing base Yukawa, exterior projection, coordinate maps and mass formula.

## Construction And Result

The two identical antifundamental copies admit equivariant flavor maps

```
((z, f), g) -> ((0, A*f + B*g), C*f + D*g).
```

`flavor` proves equivariance under the actual full SU(6) action. Mixed and
diagonal pullbacks of the existing base Yukawa then define `coupling a b u v w`.
These are couplings on the unchanged scalar representation, not masses
introduced as new inputs. The factors u/2 and w/2 compensate for symmetric
diagonal pullbacks; the resulting diagonal mass entries are u and w.

Write K(z,f) for `fivePair z f`, contraction of the exterior component with
the dual component, and t(f) for `singletCoordinate f`, its sixth coordinate.
For x=((z,f),g), y=((z',f'),g'), `mass_formula` proves

```
a*(K(z,f') + K(z',f)) + b*(K(z,g') + K(z',g))
  + u*t(f)*t(f') + v*(t(f)*t(g') + t(g)*t(f')) + w*t(g)*t(g').
```

Five explicit pairs of UV vectors recover exactly a, b, u, v, w.
Consequently:

- `mass_eq_iff` and `coupling_eq_iff`: all five parameters are identifiable.
- `massMap`: a linear parameterization by `Fin 5 -> Complex` of actual masses.
- `massMap_injective` / `massMap_range_finrank`: its image has dimension 5.
- `range_realized`: every form in that image is a vacuum evaluation of an
  actual full-group invariant Yukawa coupling.
- `mass_form_zero_iff`: the generated form vanishes iff all five parameters vanish.

The generated masses are invariant under the specified residual group by
`atVacuumOn`, using the existing proved fixed-vacuum property. No new assertion
that this subgroup equals the full vacuum stabilizer is made.

## Boundary And Next Gate

This is a lower bound on the full evaluation image, not its completeness.
The concrete next upper-bound statement is that, for every allowed Y,
`Y.toLinearMap (vacuum H)` belongs to `(massMap H).range`.
Together with `range_realized`, this would classify the full generated mass
space at this vacuum without needing to classify all vacuum-invisible couplings.

The 22-dimensional full Yukawa classification and the 17-dimensional
evaluation kernel remain external calculations. Transport of the generic
27-dimensional block-kernel theorem to this actual five-parameter family,
including its residual representation, also remains open. The prior exact
two-parameter spectrum theorems are unchanged. No amplitudes, potential
minimization or different Higgs sector are included.

## Kernel Conversion

Direct proofs of the concrete coordinate formula and probe evaluations hit
deterministic kernel timeouts. Comparing elaborated types showed differences
in carrier aliases, algebraic instances and coercion proof arguments. This
does not establish a kernel bug or identify a unique low-level cause.

The accepted proof keeps the bilinear forms abstract in `mass_formula_of`
and `probe_values_of` while doing the conversions, then substitutes the
actual generated mass. Named pairing/coordinate functions and generic
evaluation lemmas avoid repeated expansion of the analytic representation.
The final model module built in approximately 4.4 seconds in the focused run.
No limits, pins, theorem hypotheses or audit exceptions were changed.
All diagnostic declarations and incomplete attempts were removed.

## Verification

- Focused build of both new audits: passed, 4248 jobs.
- Strict transitive axiom audits: 9 generic + 19 model declarations; only
  propext, Classical.choice and Quot.sound permitted.
- Existing coordinate scripts: 8 tests passed, approximately 1.3 seconds.
  These remain external cross-checks, not premises of the new theorems.
- Full `lake build`: passed, 5856 jobs; repeated after the final source edit.
  No new-source warnings; existing dependency warnings replayed.
- Layout check: 805 modules, passed. Links: 304 Markdown files, 1847 local
  links, 33 heading fragments, zero errors. `git diff --check`: passed.
- Lean LSP unavailable; used source inspection, focused builds and profiling.
  No new external sources were needed. Unrelated qque contraction scripts
  were not rerun because their covered definitions were unchanged.
