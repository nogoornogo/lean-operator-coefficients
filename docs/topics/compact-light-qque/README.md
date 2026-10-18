# Compact Continuous Residual Symmetry On Actual Light Spaces

- ID: compact-light-qque
- Status: completed
- Working branch: `proof/compact-light-qque`.
- Integration target: `master`.
- Predecessor: [compact API audit](../compact-residual-api/README.md).

## Endpoint And Inputs

Extend the four-weight qque source theorem from finite H to compact continuous
H. Keep the original actual source, torus unitarity, strict commuting action,
invariant symmetric mass, two actual conjugators, and matching at 0, 3, 8, 14.
Add a topology on H with continuous residual action and a continuous nonzero
finite-dimensional Q target. Do not assume H-unitarity, a chosen common
constituent, or a chosen light projection.

The conclusion remains a nonzero H-invariant functional on the ordered tensor
of the four actual light sectors. No full SM/Lorentz/Grassmann nonvanishing,
generated coupling or decay rate is asserted.

## Bounded Milestones

1. Prove algebraic dual-action continuity with compatible finite-dimensional
   norms, and continuity on the radical and weight subspaces.
2. Derive semisimplicity from compact unitarization and extract actual split
   irreducible quotients. Replace finite character counting by the audited
   integral identity.
3. Assemble the compact four-weight qque endpoint; retain the finite theorem
   and verify a finite/discrete compatibility control.
4. Persistent axiom audits, focused/full builds, layout/link checks, update
   proof/assumption documentation, commit and integrate.

## Stop Gate

Reuse the audited Haar/Hom-dimension route. Do not upgrade dependencies or
start new foundational theory. Stop and name any theorem-level obstruction or
needed physical assumption change. The E6 literature boundary is unchanged.

## Result

All four milestones are complete. The endpoint
`GUT.CompactLightQque.exists_qque_coefficient` derives a nonzero H-invariant
functional on the unchanged actual qque light tensor for compact continuous H.
`not_forbidsBothInternalCoefficients` follows using qque alone.

The algebraic dual carries a local induced operator norm; its algebra/module
structure is unchanged. Haar unitarization is used on an auxiliary finite
Hilbert copy, then semisimplicity is transported back to the original carrier.
The mass and its radical are never replaced. Common irreducible quotients and
split projections are outputs, not assumed certificates.

The final API needs continuity only of the residual source action and P_Q;
the existing Q/up/e character comparison suffices for the other slots. The
reused target carriers are normed spaces; only P_Q is required finite-dimensional
by the new endpoint. Finite/discrete recovery on the common normed domain is
proved. The old algebraic finite theorem is unchanged.

Precise statement, proof map and exclusions:
[compact light qque](../../proof/current/applications/Physics/COMPACT_LIGHT_QQUE.md).

## Verification

Verified stage 01:

- Focused build of `Math.RepresentationTheory.Unitary.Audit.AuditCompactLightContinuity`
  and `Physics.StandardModel.Operators.Audit.AuditCompactLightQque`: passed
  (3904 jobs), 6 mathematical and 8 physical/control strict transitive axiom
  checks. Only `propext`, `Classical.choice`, `Quot.sound` allowed.
- Full `lake build`: passed (5647 jobs).
- `node tools/layout/check-layout.mjs`: 610 modules, passed.
- `node tools/docs/check-links.mjs`: 248 Markdown files, 1355 local links,
  32 heading fragments, zero errors. `git diff --check`: passed.
- Existing linter warnings are replayed; no warnings from the eight new Lean
  files. Pins and audit allowlists unchanged. No `sorry` or new axioms.

Lean LSP MCP was unavailable; source inspection and focused compiler checks
were used. Temporary logs in `/tmp` are disposable. All reusable proof and
audit code is registered in `Math.lean` or `Physics.lean` and source controlled.

## Integration And Remaining Boundary

Integration target is `master`; Git ancestry records the merge. Retain the
topic branch. No remote push is requested.

No work remains for this bounded qque connection. A compact duql/pair endpoint,
noncompact arbitrary actions, full gauge/Lorentz/Grassmann operators, anomaly
consistency and generated amplitudes are not proved here. These are separate
topics, not implicit continuation of this task. The E6 literature boundary and
existing model-specific assumptions remain unchanged.
