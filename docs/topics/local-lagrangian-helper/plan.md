# Frozen Helper Contract

## Purpose And Input

The user adds a local interaction once; the helper generates the associated
Euler expressions, boundary currents and EOM relation source. It reuses field
component labels, the actual exterior/polynomial jet algebra and existing
quotient/coefficient operations. No EOM formula or first-variation identity is
required as caller input. Existing direct EOM and nonderivative APIs remain.

The admitted syntax consists of complex constants, odd/even field jets with
finite derivative words, addition and multiplication. Provide ordinary Lean
arithmetic notation, powers and a total-derivative operation. Finite sums and
arbitrary finite field degree/derivative order are admitted; no fixed cutoff,
kinetic regularity or nondegeneracy premise is introduced. Jets evaluate into
the existing commuting-direction algebra. Coefficients are fixed complex
numbers, not necessarily polynomials in physical parameters.

This is an algebraic expression helper, not a text parser, automatic index
contraction search, Hermiticity checker or numerical solver. A user still
chooses fields, contractions and a requested symmetry. Nonpolynomial field
functions and analytic/integrated actions are outside this contract.

## Finite Deliverables

1. A reusable finite expression presentation with actual mixed-jet evaluation,
   total-derivative compatibility and parity involution. Odd generators obey
   the existing exterior relations; bosons use existing polynomial jets.
2. A syntax-directed first variation and an automatic finite list of
   variation-jet coefficients. Prove their equality for every expression and
   every parity-preserving field variation. Grassmann signs must follow from
   actual exterior multiplication, not an assumed first-variation formula.
   Also compare with any actual compatible evolutionary derivation where
   available. No analytic variation premise is imported.
3. Recursive formal adjoints for arbitrary derivative words and explicit
   finite-support currents. Prove the pre-quotient identity
   `delta L = sum_s eta_s * Euler_s(L) + divergence(current)`.
   The compiler and identity apply to the entire admitted syntax.
4. A two-sided differential equation relation submodule for the mixed algebra,
   closed under multiplication and all total derivatives, with minimality.
   Prove its commutative specialization equals the existing differential EOM
   ideal viewed linearly. Divergences remain a linear range, not its ideal.
5. Optional factories returning the existing `DerivativeInterface.Input`:
   automatic trivial-action entry, and a represented entry reusing a supplied
   combined-relation stability certificate. Symmetry preservation is a
   separate obligation, not inferred for arbitrary L. Prove on-shell/IBP
   vanishing of the generated first variation and compatibility of the
   commutative relation route with the previous equations factory.
6. Compiled usage controls: adding a higher scalar potential term; a
   derivative interaction and a higher derivative; mixed Yukawa interaction
   and odd-field reordering/square-zero controls. Include zero, a total
   derivative and degenerate inputs. Show exactly which expressions and
   proof arguments callers supply, and distinguish reduced derivation work
   from unmeasured claims about overall usability.

For the scalar usability control, include the existing actual Lorentz action:
a signed four-direction kinetic density plus a sixth-power potential, with
the symmetry certificate packaged once and the coupling as the caller's only
argument. This is a bounded consumer of the general compiler, not a claim
that arbitrary interaction symmetry is inferred automatically. Register its
Physics source and a separate strict layer/axiom audit in `Physics.lean`.

## Verification And Stop

Primary route: structural differentiation, actual mixed parity identities,
finite variation terms and repeated algebraic Leibniz/IBP. Use existing
commutative EOM APIs through a proved specialization, rather than changing
their hypotheses. New helpers must stay within these algebraic interfaces.

Register sources and strict transitive axiom audits in `Math.lean`. Run focused
checks, the persistent audits, layout/topic/metadata/link checks, diff review
and one serialized full `lake build`. Use the existing bounded wrapper for
expensive checks: four Lean threads, 16 GiB address-space cap and a 540-second
wall-clock timeout per command. These are execution guards, not theorem bounds;
do not raise Lean heartbeat/recursion limits to make an example pass.

Stop successfully after all deliverables, honest scope/input documentation
and a coherent verified commit. A failure requiring new analytic foundations,
dependency changes or a different physical scope requires a user decision.
Completion does not authorize a merge or push.
