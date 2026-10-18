# Polynomial Generation Criteria

## What This Closes

The parent result required actual inputs isolating every mediator path to
turn nonzero selected paths into realizable coefficients. This result removes
that hypothesis for a specific structural class: finitely many fixed paths
with polynomial weights in free coordinates. It proves the full cancellation-
aware criterion without substituting arbitrary independent Wilson coefficients
for the generation map.

The overall research objective remains in progress. In particular, neither
polynomial dependence nor a mediator factorization is inferred solely from
residual representation overlap. The theorem classifies families with the
specified structure; it does not derive that structure for every UV model.

## Structural Class And Criterion

Fix residual representations A, B, M, a finite index set I and intertwining
maps u_i : A -> M, v_Bi and v_Wi : M -> B. B is finite-dimensional. Flavor
identifications mu and electron are supplied as in the parent completeness
theorem. For any coordinate type S choose polynomials p_i over complex numbers.
For x : S -> complex let the residual coefficient pair be

```text
sum_i p_i(x) * (v_Bi composed with u_i, v_Wi composed with u_i)
```

The independent SM coefficient equivalence reconstructs a full coefficient
from this pair. The chosen free-coordinate input domain can be the full
product or a product of infinite coordinate subsets. All coordinates must
be independently available within that product; an arbitrary correlated
domain does not satisfy this hypothesis merely because it is infinite.

For a monomial exponent d define

```text
q_B(d) = sum_i electron(v_Bi(u_i(mu))) * coefficient_d(p_i)
q_W(d) = sum_i electron(v_Wi(u_i(mu))) * coefficient_d(p_i)

exists an allowed input with nonzero selected B/W pair
  iff exists d with q_B(d) != 0 or q_W(d) != 0
```

All paths sharing a monomial are added before testing nonvanishing. The
polynomials have finite support, so only finitely many monomials can contribute,
although the formal criterion quantifies over all exponent vectors. No
path-isolation or full coefficient-space surjectivity hypothesis occurs.

The forward implication does not need the infinite-product condition; the
reverse implication uses the polynomial identity theorem on that product.
It proves existence, not that every input is nonzero. Exceptional inputs
can still cancel, and no density/probability claim is made.

## Theorem Map

[PolynomialSelectedPaths](../../../Math/LinearAlgebra/PolynomialSelectedPaths.lean)
provides operator-independent scalar and pair selectors.

- `eval_selected`: selected synthesis is evaluation of a scalar polynomial.
- `coefficient`: extract the exact grouped selected coefficient of each monomial.
- `exists_nonzero_on_box_iff` and `exists_nonzero_on_box_iff_coefficient`:
  nonzero realization on a product of infinite sets iff the selected polynomial
  is nonzero, equivalently a grouped coefficient is nonzero.
- `exists_nonzero_iff_coefficient`: unrestricted-coordinate specialization.
- `monomial_coefficient` and `exists_nonzero_monomials_iff_path`: distinct
  monomials have their respective selected path coefficients, so some path
  is nonzero iff some input realizes a nonzero selector. Isolation is not used.
- `pair_exists_nonzero_on_box_iff_coefficient` and
  `pair_exists_nonzero_monomials_iff_path`: both monitored channels.

[DipolePolynomialInputs](../../../Physics/StandardModel/Operators/DipolePolynomialInputs.lean)
specializes both pair criteria to actual complete dipole sectors and composed
mediator paths. `realized_iff_coefficient_of_factorization` accepts an externally
supplied generation map F. Its residual polynomial factorization equality
is required only on the designated input product, not outside it.

## Controls And Limitations

[DipolePolynomialControls](../../../Physics/StandardModel/Operators/DipolePolynomialControls.lean)
reuses the two opposing B bridges and zero W maps from the parent sample.
With weights z and z squared, Lean proves that path isolation fails, the
selected pair equals (z - z squared, 0), and z = 2 gives a nonzero input.
With identical weights z on both paths, every selected pair instead vanishes.
These are exact algebraic controls, not UV models or matching results.

Input-dependent maps are covered only when a finite fixed-path expansion is
actually supplied. Non-polynomial, rational, logarithmic or conjugate-dependent
expressions are not automatically included as polynomials in the given complex
coordinates. A different parameterization must be justified, not presumed.
Symmetry constraints correlating coordinates require a separate domain analysis.

Mass-basis derivation, matching/RGE, loop normalization, photon combination,
rates and experimental bounds remain outside scope. Nonzero B/W selection
is still not a necessary-and-sufficient condition for a physical decay.

## Verification

- Planning commit: `checkpoint 01`.
- `lake build Physics.StandardModel.Operators.Audit.AuditDipolePolynomialInputs`:
  passed, 3554 jobs, no new-source warnings.
- [Persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditDipolePolynomialInputs.lean):
  16 strict transitive axiom checks; only propext, Classical.choice and
  Quot.sound. Imports from the model layer are rejected.
- `lake build`: passed, 5915 jobs. Existing warnings replayed; no warning
  in the new source files.
- `node tools/layout/check-layout.mjs`: passed, 862 modules.
- `node tools/docs/check-links.mjs`: passed, 321 Markdown files, 1964 local
  inline links, 33 heading fragments and zero errors.
- `git diff --check` and staged diff check: passed.
- Lean LSP MCP unavailable; source reads and CLI builds used. No custom
  axioms, `sorry`, dependency/pin changes or audit allowlist exceptions.
- No merge, branch deletion or remote push. The unmerged parent target
  remains `proof/clfv-dipole-input-structure`.

## Remaining Research Work

The input-side non-isolation issue is closed for the stated polynomial class.
Next, connect this criterion to structural construction of the paths and
flavor bridges themselves, or justify a finite polynomial expansion for a
specified family. That is distinct from proving the already stated
factorization implication and must not be reported as completed by this audit.

The unmerged [coupling-model extension](../clfv-dipole-coupling-model/results.md)
now derives the path decomposition for a specified compositional kernel class
with finite coupling spaces. Its bilinear coefficient law remains distinct
from a physical matching calculation; it does not close that boundary.
