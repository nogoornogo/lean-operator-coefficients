# Qque Coefficient Completeness

- ID: qque-coefficient-completeness
- Status: completed
- Checkpoint detail: completed; integration tracked by Git ancestry.
- Working branch: `proof/qque-coefficient-completeness`.
- Integration target: `master`; do not integrate an incomplete endpoint.

## Endpoint

For finite-dimensional complex multiplicity representations Q, Uc and Ec,
identify the independently specified derivative-free qque sector of invariant
alternating four-field coefficients with
`Hom_H(Sym^2 Q, Uc tensor Ec)`. The field model uses the existing standard
gauge representations, left/right spinors and dual conventions. Transport
the result through actual light-field identifications. No new assumptions on
constituents, conjugations or positive indices belong to this classification.
Compact continuous actions are needed for the optional irreducible-support
criterion, not silently for elementary tensor identities.

## Stages

1. General symmetric residual coefficient assembly and injectivity after
   gauge/spinor contraction and alternating descent.
2. Define the qque sector independently by species degree (2,1,1), prove
   exhaustiveness of gauge/spinor contractions, and construct the inverse.
3. Connect the symmetric-square Hom description, actual light fields and
   existing sufficient-condition routes; audit hypotheses and verification.

An image-defined sector is not an acceptable substitute for stage 2.
All-degree operators, vacuum-derived H, Wilson coefficients and dynamics are
excluded. Stabilizer classification is separate from this bounded endpoint.

## Verification

The first milestone (`checkpoint 01`) passed focused builds, eight strict transitive
axiom checks, the existing seven exact qque tests, and a full build (5743 jobs).
The next milestone adds the residual Hom isomorphism and independent sector;
its audit passes eighteen checks and its full build passes 5748 jobs.
The third milestone (`checkpoint 02`) proves ordered reconstruction and spinor uniqueness;
its audit passes 25 checks and its full build passes 5751 jobs. The final milestone
proves full surjectivity, the sector isomorphism and actual-field transport;
41 strict axiom checks, ten exact computational tests and the full build
(5758 jobs) pass.
See [results](results.md) for commands
and the exact remaining boundaries. No LSP tool is available in this session.
Dependency pins remain unchanged.

## Result And Boundaries

All three stages are proved. `QqueCoefficientCompleteness.fromHom_surjective`
and `equiv` close the independent-sector classification. `onFieldsEquiv`
transports it to actual participating fields; `hasNonzeroAlternation_iff`
connects all existing endpoints with the same actual-field identifications
to the necessary-and-sufficient Hom test. No new positivity, constituent,
conjugation or compactness premise was introduced.

There are no remaining obligations for the bounded endpoint. Computing a
model's H, deriving its field identifications, classifying compact irreducible
overlap, stabilizers, other operator species or derivative quotients remain
separate tasks. The theorem is not a decay-amplitude claim.
