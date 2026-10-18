# Frozen computable-character plan

## Scope and theorem shape

Keep Lean/dependency pins, three-generation carriers, all ten signed species,
the six-coordinate torus and positive roots unchanged. Local compact actions
include independent left/right spin groups. Supplied residual flavor actions
remain outside local counting; existing q/l charge separation handles their
scalar cyclic specialization. No arbitrary residual-action classification.

Proposed interfaces below are targets, not existing declarations:

    Counts := Fin 10 → ℕ
    Weight := Fin 6 → ℤ
    computablePolynomial : Counts → ℕ → ℤ → (Weight →₀ ℤ)
    computableMultiplicity c m delta :=
      CompactWeylExtraction.constantTerm SMCompactTorus.roots
        (computablePolynomial c m delta)

For every word `p`, `m`, `delta` and supplied residual flavor actions, prove:

    Presents (SMCompactMultiplicity.model flavor p m delta)
      SMCompactTorus.inclusion.toMonoidHom SMCompactTorus.monomial
      (computablePolynomial (SMIteratedContent.counts p) m delta)

This presentation is unconditional. Under the same `TorusReduction` input,
prove the actual kernel finrank equals the extracted integer (or its `toNat`),
rank equals the proved column count minus multiplicity, and local allowance
iff multiplicity is positive. Full q/l tests additionally require charge zero;
original Higgs counts use the already proved bounded constituent reduction.
No computed value or missing `Presents` certificate may be supplied as a
replacement hypothesis of this endpoint.

Do not require equality to the noncomputable spectral polynomial as a new
prerequisite: the extraction API accepts any polynomial with proved `Presents`.
An equality theorem may be added only if useful and available within scope.

Implementation refinement: pinned mathlib's `Finsupp`/monoid-algebra operations
are noncomputable. Executable functions therefore return finite integer term
lists and evaluate their coefficients directly; `polynomial` is their
proof-only `Finsupp` view. Proved coefficient/evaluation identities connect
the two. No oracle enters `multiplicity` or the q/l Boolean test. The semantic
target and external-premise boundary remain unchanged. The initial reference
include/exclude algorithm retains repeated weights; sparse aggregation/memoized
tables are optimizations, not assumed correctness certificates.

## Milestones

1. **Computable algebra and exact recurrence.** Use executable finite integer
   weights and sparse convolution (inspect mathlib's additive monoid algebra /
   `Finsupp` APIs). Define exterior degree tables by include/exclude recurrence:
   adjoining a slot of weight w adds its shifted degree-(n-1) coefficients to
   degree n. Prove the finite-product/subset identity. Handle repeated flavor
   weights, empty content and degrees above capacity. Generic algebra belongs
   under Math; fixed SM dictionaries belong under Physics. Prove correctness
   for a simple executable reference algorithm before optional grouped DP or
   complement-degree optimizations. Avoid classical choice in executable code.

2. **Actual six-coordinate slot weights.** Construct explicit simultaneous
   torus eigenbases for each actual compact species carrier, including color
   fundamental/dual weights, weak weights, the active left/right spin factor,
   integral hypercharge and three flavor copies. Prove their action identities
   against `SMCombinedCompactAction.field` and `SMCompactTorus.inclusion`.
   Pilot L and conjugate L, then Q and all other species. The existing weak
   basis alone is insufficient; a full joint action certificate is required.
   Inverting the torus negates every weight. Signed conjugation negates gauge
   weights and swaps the active spin factor, not all six coordinates blindly.

3. **Exterior and arbitrary-content semantics.** Reuse
   `ExteriorCharacterPolynomial.exterior_character` for the proved diagonal
   bases and transport the DP evaluation to that formula. Reuse the existing
   content decomposition and character product to cover all ten species and
   arbitrary orderings. Check the compact independent-spin action transport;
   the older paired-Weyl character identity is not automatically the required
   compact identity. Combine the Higgs weights `m,m-2,...,-m` with hypercharge
   `3*delta`; prove evaluation equals the actual inverse model character.
   Close the target `Presents` theorem without the Weyl premise.

4. **Conditional executable extraction and consumers.** Apply the existing
   `SMWeylExtractionInput` consumers to the new polynomial. Prove kernel/rank/
   positivity theorems and connect them to `SMQLCompactMultiplicity` and the
   actual request domains. Separate computable per-entry tests from the
   universal/existential request semantics. A finite domain need not be small
   enough to enumerate. Preserve the unconditional charge-only shortcut and
   all existing generic, charged-Higgs and prescribed-LFV interfaces.

5. **Bounded evaluation and verification.** Start with LLHH/conjugate LLHH,
   empty/top powers, charged/parity controls and a mixed-species example.
   Then assess evaluation of the 107 neutral constant-content entries, using
   Lean kernel-checked computation and conditional soundness theorems. Compare
   with the persistent Python diagnostic as an independent supplement. Do not
   silently turn its output into a certificate or enable `native_decide`.
   Only extend the exported certified table after checking its theorem scope.
   Any 572-assignment run must name the checked content/target range; bounded
   charge predicates do not establish all-degree request satisfaction.

## Acceptance and stopping conditions

The primary endpoint is the uniform computable `Presents` theorem and its
actual conditional kernel/support consumers. Numerical tables are outputs,
not proof foundations. Executable arithmetic must compile without a classical
oracle, custom axioms, `sorry`, audit exceptions or changed resource limits.
The Weyl law remains an explicit documented literature theorem parameter;
proving compact Lie geometry or the Weyl integration formula is excluded.

Stop and record the exact obligation if joint weight semantics cannot be
closed with existing basis/exterior/trace interfaces and would require a new
foundational project, if a source convention disagrees with the diagnostic,
or if changes to pins/physical scope/external premises become necessary.
Do not substitute a conditional basis or presentation premise for the frozen
endpoint. Slow bounded computations can be deferred without invalidating a
proved uniform theorem; record their limits rather than expanding resources.

Do not enumerate the trillion-size content box or ordered-word universe.
Efficient search of all q/l requests needs a separately assessed compression
and support-search strategy; it is not implied by this per-content evaluator.
Derivatives/EOM/IBP, additional Higgs copies/actions, UV realization, matching
and rates remain outside scope. New model searches are not authorized.

For each implementation milestone run focused builds and persistent strict
transitive audits, then one serialized `lake build`, layout and link checks,
exact diagnostics and diff/assumption review. Register sources/audits in the
appropriate aggregates and update the topic and assumptions ledgers. Commit
verified milestones; merge/push requires separate user direction.
