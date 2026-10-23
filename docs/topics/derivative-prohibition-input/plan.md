# Frozen Implementation Contract

## Actual Input And Hypotheses

Use `Math.DerivativeInterface.Input H U` unchanged. Its actual coefficient
space is equivariant functionals annihilating its specified stable relation
module; its source Q is the actual quotient U/T. All detection and constituent
conditions concern Q and its induced action. Group H is the specified group
being tested; a residual-only physical use must already account for the
local symmetry in its source. A generic scalar-action premise does not
automatically hold for a full Lorentz action.

No finite-dimensionality, invariant complement, semisimplicity, nonzero
carrier or nonderivative/on-shell degree decomposition may be inferred
silently. State each needed assumption in the actual theorem. The generic
package applies to graded, full-EOM and helper-generated common inputs;
particular models still retain their input/covariance conditions.

## A — Quotient-Level Necessary Conditions

Define prohibition/allowance on P.Coefficient and connect them to P.residual
Hom using the existing inverse equivalence. Prove:

- Under explicit scalar action on Q and Nontrivial Q, prohibition iff a
  group element detects the scalar character. Without that instance, give
  a support-guarded iff: Nontrivial Q implies detection. Zero quotients
  require no detecting charge. Also permit scalar action on U as a sufficient
  way to obtain the required quotient action.
- Under explicit semisimplicity of the actual quotient representation,
  prohibition iff it shares no irreducible constituent with the trivial
  target. Expose the corresponding nonzero-witness obstruction.
- For an arbitrary indexed family of actual inputs and a selection predicate,
  all selected inputs forbidden iff their supported scalar actions are
  detected. This is a logical family theorem, not a computable support
  classifier, independent decomposition or finite cutoff.
- Zero-derivative graded input agrees with the existing nonderivative
  coefficient prohibition criterion before imposing EOM.

## B — Relations And Source Transport

For a further stable relation submodule, construct its sum with P.relations.
Prove the injective forgetful map on coefficients and its evaluation law;
prohibition before adding relations implies prohibition afterwards, and
allowance afterwards implies allowance beforehand. Give a generic
coefficient-equivalence transport criterion without requiring an invariant
complement. Do not claim the reverse monotonicity.

## C — Selected Targets And Extension Boundary

Define global target prohibition as every global coefficient vanishing on
an invariant subspace V. Distinguish it from prohibition of every coefficient
of P.select V. Prove:

- Selected-input prohibition implies global target prohibition.
- The converse holds when the actual restriction map is surjective.
- Global target prohibition and an allowed selected coefficient imply
  failure of restriction surjectivity.
- Conditional scalar detection/common-constituent consequences for selected
  input, keeping the extension and support premises where needed.

Include a fully specified two-dimensional unipotent action with a fixed line:
global invariant functionals vanish on the line, but that line itself has a
nonzero invariant coefficient. This refutes dropping the extension premise.
No general semisimple splitting/extension project is needed for this boundary.

## D — Actual Consumers And Negative Controls

1. Reuse the actual one-direction quadratic scalar example: IBP-only source
   has a nonzero coefficient; adding the free EOM kills it. Record the neutral
   action and zero quotient, refuting an unguarded charge necessity and the
   reverse of relation monotonicity.
2. Give a neutral nonzero supported input and a genuinely detected scalar
   action control, so the character criterion is not checked only vacuously.
3. On the existing actual Lorentz scalar input with equation
   wave phi + lambda phi cubed, show wave is already an IBP relation. For
   nonzero lambda, every coefficient evaluates phi cubed to zero; existence
   of a global coefficient nonzero on phi cubed therefore requires lambda=0.
   This is a necessary parameter condition, not a complete scalar-model
   classification or an assertion that every selected coefficient extends.

## Gates And Stops

Only additive Math/Physics sources and aggregate registrations are planned;
existing nonderivative signatures, dependency pins and audit allowances stay
unchanged. No `sorry`, custom axiom or external completeness premise.
Use focused builds, namespace-wide strict transitive axiom/import audits,
one serialized full `lake build`, layout, topic navigation, metadata, local
links and diff checks. Reuse the existing two-thread, 16 GiB address-space
guard, 180-second final focused and 540-second full-build ceilings, with
default Lean elaboration limits.

The endpoint is A–D proved (including the explicit counterexamples), result
and assumptions documentation, verification and coherent commits. Continue
through that endpoint; a commit is not a stop. A genuine new theorem-level
foundation, physical scope change or need to reopen the deferred literature
bridges requires an explicit scope decision. Do not start them recursively.
Do not merge into master without a separate instruction.
