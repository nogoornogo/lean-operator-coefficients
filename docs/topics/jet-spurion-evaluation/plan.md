# Jet/Spurion Connection Contract

Status: frozen before source implementation.
Working branch: `proof/jet-spurion-evaluation`.
Parent and integration target: `proof/derivative-ibp`. This is a bounded child
exception; it does not authorize integration of either branch into master.

## Statement And Inputs

Let `L` be an arbitrary local group, `H` a finite residual group, and `U` an
actual fixed-grade jet source after its proved IBP or scalar EOM/IBP relations.
Construct a representation of `L × H` on `U` from internal field actions of `H`
and direction actions of `L`. Product restriction gives commuting local and
residual actions. Define the local coinvariant quotient `Q` from this actual
action, and prove it finite-dimensional from the existing fixed-grade results.
No compactness, local averaging or invariant-exactness assumption is permitted.

A finite-dimensional spurion representation `S` of `H` and every specified
`s ∈ S` determine the actual stabilizer `H_s`. Prove a two-way coefficient
identification between local-invariant, `H_s`-invariant functionals on `U` and
`Hom_(H_s)(Q, ℂ)`. Compose with the existing finite-group polynomial evaluation
to prove surjectivity at every value, with sufficient spurion total degree
`orbitSize(s)-1` and uniform bound `|H|-1`. The quotient-dual coordinates are
chosen by a finite basis, not supplied as a new completeness premise.
Evaluation and inverse formulas must refer to actual source representatives.

## Actual Jet Interfaces

1. Scalar EOM: use the symbol `q`, all its descendants, the existing free
   quotient algebra and actual on-shell divergence range. The generic local
   action requires the existing explicit `q`-invariance input; do not assume
   arbitrary equations covariant. Construct the internal/direction product
   action and the combined off-shell EOM/IBP representation equivalence.
2. Mixed off shell: use the actual exterior/polynomial algebra, grade and
   derivative range. Connect its existing exterior/symmetric tensor source
   through the proved grade equivalence. No mixed fermion EOM is introduced.
3. Lorentz consumer: specialize the scalar interface to the existing Pauli
   SL(2,ℂ) dual direction action and massless wave symbol. Symbol invariance
   is proved in the parent. Local Lorentz symmetry remains arbitrary/noncompact
   in the common bridge and is not averaged with the finite residual group.

Use finite component and direction sets only for finite fixed grades; jet
orders themselves remain unbounded. The spurion field is constant, transforms
under the residual group, and is neutral under the local group. Its total
polynomial degree is not an operator mass dimension or a derivative cutoff.

## Complete Nonzero Consumer

Reuse the fully proved mixed example with one odd field `ψ`, one even field
`φ`, one direction and grade `(2,1,2)`. Its complete quotient is the complex
line, represented by `A=φ₁ψ₀ψ₁`, with `[φ₀ψ₀ψ₂]=-[A]` and `[A]≠0`.
Construct the actual two-element group action fixing `ψ` and changing the sign
of `φ`, and prove its action on the entire quotient is the sign character.
Use a one-dimensional sign spurion. At zero value all invariant coefficients
must vanish. At every nonzero value the stabilizer is trivial and a degree-one
covariant evaluates to a nonzero coefficient. Prove that degree-zero
covariants have zero evaluation, so the degree-one control is substantive.
The example has positive derivative order and actual Pauli/IBP relations;
its trivial local action is explicit. The Lorentz specialization is a separate
checked consumer, not an assertion that this one-direction example is 4D.

## Routes, Resource Envelope And Stop

Primary route: compose the existing local-coinvariant coefficient equivalence
with bounded finite-group evaluation, then instantiate actual product jet
representations. Fallback: transport the same quotients through their proved
representation equivalences before evaluating. Both routes keep the same
actual source, assumptions and endpoint. Do not substitute a supplied quotient,
relation matrix or source-basis completeness for an unresolved connection.

Keep all pins and default elaboration/kernel limits fixed. Heavy builds use
four Lean threads, a 540-second timeout and a 16 GiB inherited per-process
address-space limit. Disposable output remains outside source control.
Require focused builds, strict transitive audits, a serialized full `lake build`,
layout, local-link, topic-index, portable-metadata and diff checks. Preserve all
parent proofs and audits, reconcile bibliography and assumptions, then commit.

Stop successfully only when all deliverables pass. A failed actual-source or
finite-coordinate bridge within these two routes yields a documented bounded
stop rather than new assumptions. Stop for a scope decision before changing
pins, enlarging resource limits or reopening excluded foundations. General-group
saturation, minimal operator dimensions, Weyl/interacting/gauge EOM, numerical
phenomenology, UV matching, amplitudes and full EFT tables remain excluded.
