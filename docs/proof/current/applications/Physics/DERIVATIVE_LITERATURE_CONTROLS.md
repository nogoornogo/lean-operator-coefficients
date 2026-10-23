# Bounded Derivative Literature Controls

These theorems compare specified algebraic readings with derivative input
operations. They establish one complete finite polynomial substitution
example and narrower scalar, Higgs and mixed sign/relation certificates.
They do not establish complete derivative SMEFT bases.

The table below records the original comparison inputs. The subsequent
[foundation topic](../../../../topics/derivative-literature-foundations/README.md)
adds the [actual generated Higgs input](../../inputs/Physics/HIGGS_LAGRANGIAN_INPUT.md),
[finite source certificates](FINITE_DERIVATIVE_CERTIFICATES.md), and
[paired Weyl generated input](../../inputs/Physics/PAIRED_WEYL_LAGRANGIAN_INPUT.md).
Its degree-zero scalar image and generated/direct input connections are
proved independently. Positive-derivative basis counts and the physical
C5 current dictionary remain partial; those new inputs do not retroactively
change the original trivial-action statements below.

## Certified Statements

| Source reading | Lean result | Exact scope |
| --- | --- | --- |
| One-dimensional free scalar | [Math scalar controls](../../../../../Math/RepresentationTheory/Jets/DerivativeLiteratureScalar.lean), `off_dimension`, `on_dimension`, `on_coefficient_zero` | Actual one-species, two-field/two-derivative IBP quotient has dimension 1; adding the free second-derivative equation gives dimension 0 and zero coefficients. |
| Four-dimensional scalar | [Finite scalar completeness](../../../../topics/scalar-derivative-completeness/results.md); [order-four successor](../../../../topics/scalar-quartic-four-completeness/results.md) | Every admitted coefficient on the complete two-derivative Lorentz grade vanishes. The entire four-field/four-derivative invariant coefficient space is equivalent to the complex numbers by K-squared evaluation, with an explicit normalized inverse. |
| Gaugeless Higgs reduction | [Math Higgs controls](../../../../../Math/RepresentationTheory/Jets/DerivativeLiteratureHiggs.lean), `literal_reduction`, `normalized_relation`, `selected_extraction` | Exact component-polynomial EOM identity, full differential relation and restriction on a five-representative span; no physical group/dagger or helper-generated doublet equations are assumed proved. |
| Higgs four-derivative candidates | Same Math source, `probe_values`, `raw_independent`, `probe_not_ibp` | Three polynomials are independent before quotient. One raw probe detects a total derivative, so no quotient independence/completeness follows. |
| Weyl/Higgs current reading | [Physics mixed controls](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/DerivativeLiteratureMixed.lean), `current_reorder`, `current_ibp` | Actual exterior sign and ordinary even total-derivative IBP. This input is off-shell and has trivial residual action; the physical Weyl current/dagger dictionary is unproved. |
| Polynomial first-order expansion | Physics scalar controls, `quartic_euler`, `quartic_relations`, `extraction_agrees`, `substitution_second`, `second_raw_nonzero` | Actual quartic scalar helper/direct-EOM agreement and polynomial substitution through order two for the stated Lorentz model. |

## Renewed Literature Consumers

The subsequent [proof-based recheck](../../../../topics/derivative-literature-foundations/literature-recheck.md)
uses [persistent consumers](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/DerivativeLiteratureRecheck.lean)
under namespaces `Physics.DerivativeLiteratureRecheck.C1` through `C6`:

- C1 decodes admitted finite rows (c,-c) and proves on-shell coefficient
  vanishing through the complete actual-source presentation. C2 combines
  the complete degree-zero image with the narrower positive-degree controls.
- C3 maps real paper parameters to a=-m2, b=lambda and proves the exact
  signed relation in the full generated quotient and for every actual
  global SM/Lorentz coefficient. `derivative_only_iff` states when omitting
  potential values is valid. No nonzero-value witness or actual-group finite
  five-candidate presentation is asserted.
- C4 proves the explicit divergence is zero in the free represented input
  and rejects probe 0 as a full-input coefficient. Raw independence remains
  distinct from quotient independence and invariant completeness.
- C5 proves the literal current divergence is a combination of both Weyl
  equation families. `conserved_products` kills arbitrary products in the
  generated input, and `symmetric_current_zero` uses EOM plus IBP. These
  conservation identities establish no physical-current equivariance,
  bidirectional-candidate nonzero support, Higgs EOM or mixed internal action.
- C6 tests first-order vanishing under every generated coefficient and
  retains the raw second-order nonzero control.

These checked extensions do not change the original input statements in
the table. The renewed primary-source register and verification are linked
from the recheck report; no literature count becomes an assumption.

The [C5 successor](../../inputs/Physics/WEYL_HIGGS_CURRENT_INPUT.md) proves
the combined free Higgs/both-Weyl input, actual weak/hypercharge and Lorentz
stability, the two-/four-component current dictionary and full density
invariance. The union of generated Euler families has the same complete
relations as the component input, with inverse coefficient transport.
Li (4.24), Murphy Table 5 and DHM G.1.82/footnote 127 agree within this
native reading. The entire selected coefficient space now has a complex
linear equivalence with ℂ, normalized inverse, both inverse laws and dimension
one; full-quotient support is nonzero. The whole-source upper and invariant
Grassmann-wave lower supply these proofs. The rank-55 matrix remains an
independent diagnostic, not a premise. This is a free one-flavor specialization.

## Inputs And Conventions

The [nonderivative input recheck](../../../../topics/derivative-literature-foundations/nonderivative-recheck.md)
adds actual old-input usages in
[Math checks](../../../../../Math/RepresentationTheory/Jets/NonDerivativeInputChecks.lean)
and [represented model checks](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/NonDerivativeModelChecks.lean).
Original exterior/symmetric coefficients round-trip through the zero-degree
entry, preserving evaluation and nonzero/forbidden conditions for arbitrary
actions and counts. Concrete determinant/product and finite-local controls
have actual supplied coefficients; their Unit group is not a physical SM
dictionary. Actual Lorentz scalar powers and the stable Higgs potential
selection exercise the EOM entry on nonderivative targets, retaining the
full relation preimage and the cubic-value condition lambda*c=0. No complete
Higgs potential basis or universal selected-coefficient extension follows.

The scalar sources are the existing untruncated ordinary jet polynomial
algebras over the complex numbers. Free one-dimensional EOM is the second
derivative seed and all descendants/products. Four-dimensional scalar
controls use the actual SL(2,C) Lorentz direction action, signature (+---),
with wave phi + g phi cubed as leading equation. Common coefficient operations
descend through the actual linear relation module. IBP is a divergence range.

The Higgs controls use four independent component labels (two H and two
formal conjugates). Their seeds are Box H + a H + b rho H, including the
formal conjugate-label family with the same a,b. The algebraic statements
hold for arbitrary complex a,b; a physical Hermitian interpretation needs
the separately specified real-coupling and dagger dictionary. Their concrete
input uses trivial residual action. The raw four-derivative probes need not
annihilate IBP; a checked witness shows that they do not.

The mixed reading uses the actual exterior algebra of four odd component
labels tensored with the polynomial algebra of four even component labels,
with the existing Pauli matrix convention and four ordinary derivative
directions. Its input imposes actual IBP only. No free Weyl equations,
Lorentz/weak invariant basis, physical charge conjugation or real Hermitian
coefficient count is included in that result.

The complete scalar example fixes

\[
L_0=\tfrac12(\partial\phi)^2-\tfrac g4\phi^4,
\qquad \phi\mapsto\phi+\varepsilon\phi^3.
\]

The helper Euler coefficient is minus the direct equation seed. Equality
of differential ideals handles this normalization, and both coefficient-map
inverse laws and evaluation agree for the actual Lorentz action. The first
coefficient has the explicit Euler/divergence formula. The second is
9/2 times phi to the fourth times the kinetic contraction, minus 3g/2 times
phi to the eighth. Raw nonzero at g=0 is not nonzero after EOM/IBP.

## Proof And Evidence Boundary

Proofs use source reconstruction, actual equation projection kernels,
Leibniz identities, polynomial coefficient evaluation and exact quotient
membership. No literature completeness assertion or matrix output is an
axiom. The independent exact Python diagnostics are supplementary; their
finite presentations have no proved semantic bridge for the remaining
multi-content/invariant count claims.

See [source locations and coverage](../../../../verification/derivative-interface-coverage.md),
[case results](../../../../topics/derivative-literature-comparison/results.md)
and [strict audit/build evidence](../../../../topics/derivative-literature-comparison/verification.md).
Analytic actions, amplitudes, full covariant SMEFT, quantum equivalence,
matching and phenomenological predictions remain outside these statements.

## Additional Input, Presentation And Reality Checks

The [additional report](../../../../topics/derivative-literature-foundations/extended-checks.md)
records all four user-directed checks. The actual Lorentz epsilon coefficient
on two left-Weyl inputs and any number of neutral scalar spectators round-trips
through old and integrated zero-degree entries. Its normalized/exchange values
are 1/-1. One Weyl input with any number of such spectators is forbidden by
the actual central minus identity. These are off-shell Lorentz tests, not SM
Yukawa or interacting mass classifications.

`Math.InputPresentation` transports quotient sources and coefficients under
an equivariant linear equivalence carrying the full relation module. Values
and inverse maps agree. A general source basis change conjugates the action
and maps all relations; it does not preserve an arbitrary fixed action by
assumption. Nonzero common seed scaling and elementary row addition preserve
the full two-sided differential closure and linear IBP. Concrete two-species
equation and relabel controls instantiate these laws.

`Math.TwoSpeciesDerivativeChecks` uses the actual unbounded one-direction
free jet algebra and both second-derivative equations. At d=0, weighted
support reconstructs the complete source at each content (r,s); a global
relation-annihilating functional and both inverse laws give actual image
dimension 1. At content (1,1), d=2, complete exponent classification gives
three monomials and EOM/IBP kill all three, proving image dimension 0.
The [C1/C2 successor](../../../../topics/scalar-derivative-completeness/results.md)
adds complete C1 positive-degree sectors (1,1),d=1 and (2,2),d=1,2, each of
dimension 1, with actual-image/coefficient equivalences and global arbitrary
coefficient values. For C2 it proves complete order-two coefficient vanishing
under the actual Lorentz group, and a nonzero actual K squared class at order
four. The three specified metric contractions reduce to that nonzero line.
The fixed-wave separator is not Lorentz invariant. The
[order-four successor](../../../../topics/scalar-quartic-four-completeness/results.md)
closes the complete selected invariant coefficient line by source coverage,
rank-four controls and an explicit 36-wave normalized coefficient. Its full
relation annihilation, arbitrary-group grade invariance, inverse laws and
dimension one are proved in Lean. Finite-group and infinitesimal script
ranks remain diagnostics. The un-invariant quotient is larger than the
candidate line; the paper convention bridge remains explicit.

`Physics.ScalarRealityChecks` supplies coefficient conjugation on the actual
real-coupling scalar input. It preserves the whole differential EOM closure
and IBP, is involutive, and commutes with the actual Lorentz action. The
complete free zero-degree Hermitian image is a real line; scalar coefficients
are fixed exactly when their imaginary part vanishes. Paired on-shell Weyl
adjoint/action/derivative and conjugated equation-descendant consumers use
both conjugate linear equation families. These do not establish Hermiticity
for arbitrary mixed interactions. The separate real-dimension-2 coordinate
pair control assumes independent coordinates and proves no Weyl basis count.

All new source namespaces, including support instances and definitions,
have persistent strict transitive audits. No external completeness premise
is added. The topic's [verification gate](../../../../topics/derivative-literature-foundations/verification.md#additional-input-verification-gate)
records the full build and exact diagnostic checks.
