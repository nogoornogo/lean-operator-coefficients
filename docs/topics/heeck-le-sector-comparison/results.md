# Scoped Comparison Results

## Outcome

All five planned entries have explicit normalized algebraic dictionaries and
Lean completeness certificates. No discrepancy was found within this bounded
comparison. This says nothing about other tables or the full paper.

| Entry | Matched result |
|---|---|
| DUQL | D,U,Q,L ordered contraction and distinct-species exterior inverse |
| QQUE | Q,Q,U,E contraction; exterior restriction and symmetric-Q inverse |
| QQQL | Weak (03)(12), spin (01)(23); explicit six-term orbit inverse and raw alternating descent |
| DUUE | D,U,U,E single term; U,U,D,E ordered source `(0,-swap k)` and raw alternating descent |
| Right-handed u²d⁴ | Two seeds; selected 25-vector exchange-orbit basis and typed-statistics physical inverse |

See the [completed-result dossier](../../proof/current/applications/Physics/HEECK_LE_BASIS.md)
and [coverage ledger](../../verification/heeck-le-coverage.md).
The source explicitly uses three generations. Our six-quark formal transport
works for arbitrary finite-dimensional distinct U,D, including dimension four;
it is not restricted by the separate Li printed-list flavor boundary.

## Reproducibility And Trust Boundary

`python3 tools/heeck-le-six-quark-check.py` uses Python's standard library and
exact rational arithmetic. It independently evaluates the two color products
and spin product on the local epsilon probes, selects 25 independent
exchange-word columns and proposes their inverse matrix. Its companion
`--certificate-json` prints the proposal data. Neither its rank calculation
nor its inverse checks are a Lean premise. Literal correspondence, each
exchange step, both matrix products and the resulting invariant-space basis
are proved in Lean. The generator reuses finite epsilon/probe definitions from
`tools/li-six-quark-check.py`, not that source's missing-component hypothesis.

The compact two-term list is not asserted to be a basis of 25 free flavor
maps. All four typed statistics equations remain in `StatisticsHom`.
One-generation finrank two and agreement with the existing two-probe inverse
are formally established; this topic does not add a paper-wide term-minimality
or arbitrary-flavor dimension polynomial theorem.

## Verification

- Focused build:
  `lake build Physics.StandardModel.Operators.Audit.AuditHeeckLeBasis` —
  successful, 3,350 jobs, 831 strict transitive declaration checks.
- The audit covers every declaration in the eight comparison namespaces,
  permits only `propext`, `Classical.choice`, `Quot.sound`, and checks no model
  layer is imported. Generated auxiliary declarations are included in the count.
- `python3 tools/heeck-le-six-quark-check.py` — rank 25 and both rational
  inverse products pass (supplementary exact calculation).
- `node tools/layout/check-layout.mjs` — 1,121 modules, no violations.
- Full `lake build` — successful, 6,448 jobs.
  A final replay also succeeds; its log contains no `warning:` or `error:` lines.
- `node tools/docs/check-links.mjs` — 434 Markdown files, 2,914 local inline
  links, 100 heading fragments, no errors. The checker needed sandbox
  escalation for its read-only Git child process.
- `git diff --check` — clean. Dependency pins and existing certificates unchanged.

During implementation, a missing local tensor additive-group instance caused
QQUE elaboration timeouts. Explicit existing-style instances resolved them
without retaining an increased heartbeat setting. An unavailable simp API in
DUUE and audit namespace quotation errors were corrected. These failed drafts
are not verification evidence. The rational finite data retains its bounded
kernel resource settings; no audit exception or new axiom was introduced.

## Closure Boundary

No unresolved prerequisite was needed for the five frozen entries. Do not
extend this record to other dimension-nine chiralities, derivatives, EOM/IBP,
amplitudes, AutoEFT, UV matching or rates. Root README and dependency pins
remain unchanged. The user authorized master integration;
Git ancestry records the merge. Merged-state build, audit, layout, link and
exact-script checks are repeated before local topic-branch removal.
