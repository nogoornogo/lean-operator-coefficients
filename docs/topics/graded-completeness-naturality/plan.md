# Frozen Plan

## Inputs And Non-Goals

Use the existing finite fermion/boson species sets, local group G, residual
group H, complex local and multiplicity modules, and arbitrary mixed degree
(n,m). Fields retain their local tensor residual factorization. Support
predicates are invariant under the separate fermion and boson permutations.
For bounded engineering degree, reuse the existing grading hypotheses.

Changes of field presentation are species-preserving equivariant linear
equivalences of the local and multiplicity factors. Changes of residual group
are homomorphisms j : H' -> H, with representations pulled back along j.
Keep the local group fixed in the initial endpoint. Species relabeling,
noninvertible field maps, local-group changes, new physical sectors,
derivatives, EOM/IBP, amplitude correspondence, automatic Hom computation and
finite all-degree cutoffs are excluded.

Do not define residual transport by conjugating an input map with the
completeness equivalence and call that naturality. The residual map must be
independently induced on local coinvariants and exchange quotients.

## A. Direct Transport And Quotient Compatibility

- Reuse `InvariantCoefficientTransport`, `RelationQuotient`,
  `SpeciesCoefficientTransport` and `SurjectiveHomTransport` where applicable.
- Lift species-wise factor equivalences to ordered tensors and mixed
  exterior/symmetric inputs. Show preservation of support and exchange signs.
- Show that induced maps carry local coinvariant relations and exchange
  relations to the corresponding relations, and construct residual carrier
  equivalences with formulas on quotient generators.
- For residual restriction along j, establish the identification of the
  underlying quotient carriers and the pulled-back residual actions. Do not
  confuse proof-dependent presentation differences with new assumptions.

Acceptance: independently constructed input and residual maps, with generator
formulas, inverses where appropriate, and identity/composition laws.

## B. Degree-Uniform Naturality

Let E_H be the existing completeness equivalence and T_in/T_out the direct
transports. Prove `E_target (T_in f) = T_out (E_source f)`, and its inverse
reconstruction form. Account for contravariance of coefficient functionals.

For residual restriction, the map goes from H-invariant coefficients to
H'-invariant coefficients on the same fields; the corresponding map of Hom
factors must make the same square commute.

Acceptance: arbitrary (n,m), including zero degrees, then stable support
selection and all-degree products/direct-sum functional presentations.

## C. Monotonicity And Surjective Transport

- For H_small <= H_large, construct an injective linear restriction map on
  coefficients and on the residual Hom factors.
- Prove allowance for H_large implies allowance for H_small, and prohibition
  for H_small implies prohibition for H_large. Do not claim their converses.
- For surjective j, prove the restriction maps are equivalences and commute
  with E_H. Group isomorphisms are a specialization of this case.
- Reuse the existing kernel criterion when representations must descend;
  do not infer descent from surjectivity alone.
- Apply monotonicity to nested stabilizers of specified preserved data,
  using subgroup containment as the input; no new stabilizer classification.

Acceptance: fixed degree, selected supports and all degrees; degree-bounded
statements follow with the same support predicate and weights.

## D. Regressions, Audit And Documentation

- Include a mixed fermion/boson example for field-change naturality.
- Include a small exact subgroup example demonstrating the direction of
  monotonicity and that restriction need not be surjective.
- Include a surjective-map example and a preserved-data containment example.
- Register modules and persistent strict transitive audits in aggregates.
- Run focused builds and audits, one serialized full `lake build`, layout,
  Markdown link checks and `git diff --check`.
- Write a completed-result Math dossier and update verified assumptions and
  the topic record. Do not automatically change the root README or literature
  coverage ledgers: this topic does not expand literature verification.

## Stop Condition And Decision Gates

Stop after A-D pass with direct quotient maps, commuting diagrams and the
correct monotonicity directions established and documented. This is an
integration of existing completeness, not a new operator classification.

If direct quotient transport needs a substantial new foundation, requires
extra mathematical hypotheses, or reveals an incompatibility with the existing
exchange/support conventions, report the precise obstacle before changing
scope. No master merge is authorized by completion of this plan.
