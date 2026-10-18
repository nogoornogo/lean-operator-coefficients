# Frozen Implementation Plan

## Statement And Inputs

Use `SelectionCriteria.Allowed` and `Forbidden` on the existing
`DeltaBTwoModelInterface.ModelSector up down`, not on unrestricted 25 local
coordinates. The general residual-Hom equivalence retains finite-dimensional
complex up/down carriers and all typed exchange relations.

The concrete specialization fixes both flavor carriers to complex scalar
lines. Residual action is the proved cyclic representation of charges
`u,d : ZMod N`, with `N : ℕ` and `[NeZero N]`. Gauge, chirality, degree and
hypercharge inputs remain those of the existing right-quark `(2,4)` model.
The charge convention is physical u_R/d_R, not their conjugate negatives.

Prove for the independent physical sector:

- `Allowed sector ↔ 2*u + 4*d = 0`;
- `Forbidden sector ↔ 2*u + 4*d ≠ 0`;
- under charge neutrality, a linear equivalence with `ℂ × ℂ`, retaining
  the established two-probe normalization and both inverse identities;
- under nonneutrality, every physical coefficient vanishes.

Actual fields require the existing `Inputs` equivariant identifications.
Transport both predicates through `onFieldsEquiv`; do not infer these inputs
from a model name or infer UV generation from allowance.

## Milestones

1. Inspect the scalar/trivial-action physical two-coordinate specialization.
   Prove that arbitrary scalar up/down characters act on the exterior domain
   by their degree-weighted product. Keep individual actions nontrivial.
2. Separate invariant gauge/spin structure from this total character. Prove
   necessity with a nonzero probe and sufficiency by transport of the existing
   two independent coefficients. Establish the neutral equivalence and the
   nonneutral zero theorem without assuming completeness of a candidate image.
3. Specialize using the faithful cyclic character kernel to the exact charge
   iff. Connect the general constrained-Hom certificate and actual-field inputs.
4. Combine with the previous five-charge dictionary. Prove both simultaneous
   criteria: all Delta-B-one families forbidden, LLHH allowed, and the specified
   Delta-B-two sector respectively allowed or forbidden. Include Z2 quark parity
   as an allowed-six-quark control, an independently checked forbidden-six-quark
   finite assignment, trivial charges, and order one. Choose the second finite
   example only after checking all congruences; do not impose Yukawa compatibility.
5. Persist strict audits for new endpoints. Run focused and full builds, layout,
   links and diff checks; document verified hypotheses and commit completion.

## Boundaries And Stop Condition

No new Schur-functor classification, arbitrary-generation flavor charge tables,
all Delta-B-two sectors, anomaly cancellation, quantum exactness, Yukawa
compatibility, UV generation, RGE or rates. The simultaneous statements refer
only to the previously completed Delta-B-one/LLHH domains and the specified
six-quark domain, not every operator at every degree.

Bounded scalar/exterior transport helpers are in scope. Stop for a counterexample
to the frozen scalar statement, an essential new physical hypothesis, or a large
foundational prerequisite. Do not silently strengthen the inputs or weaken audits.
Completion requires every milestone and verification gate; master merge requires
separate user direction. No implementation is claimed at the planning checkpoint.
