# Li Qqql Basis And Flavor Counting

- ID: `li-qqql-basis`
- Status: completed
- Result type: proved normalized local-contraction completeness certificate
- Working branch: `proof/li-qqql-basis`
- Integration target: `master`
- Integration evidence: Git ancestry into the recorded target; report merge outcome

## Endpoint And Scope

Certify a specified published derivative-free dimension-six `qqql` local
contraction basis against the independently defined degree-(3,1) invariant
exterior coefficient sector. Construct nonredundant finite-flavor coordinates,
prove extraction and reconstruction are inverse, and derive the dimension for
arbitrary finite quark and lepton flavor counts.

The existing starting point is
`QqqlExteriorCompleteness.Sector q l ≃ₗ[ℂ] QqqlExchange.residualSpace q l`.
The target is an exchange-constrained family of four residual functionals;
these are not four independent coefficients. Three repeated Q slots make this
a test of mixed permutation components beyond the symmetric two-Q pilot.

For arbitrary abstract residual group H, retain equivariance as explicit linear
constraints in the finite coordinates. An unrestricted operator basis and the
dimension formula concern trivial residual action. Do not infer the invariant
dimension for general H from the flavor counts alone. The existing infinite-
dimensional completeness theorem retains its original hypotheses.

Detailed phases and acceptance statements are in [the plan](plan.md).
This topic ends at qqql. Connecting duql/duue and certifying the four-family
total, higher dimensions, general p/y/m/j algorithms, package runtime output,
amplitudes and EOM/IBP are subsequent topics.

## Deliverables And Acceptance

1. A pinned paper expression and explicit field, slot, epsilon and spinor
   convention dictionary, following the completed qque pilot.
2. A Lean map from the literal candidate contractions to the independent
   physical exterior sector, with normalization and exchange signs proved.
3. Finite nonredundant flavor coordinates, with explicit two-sided inverses.
4. For trivial residual action, an independent spanning candidate family and
   a proved cardinality/finrank formula for arbitrary flavor counts.
5. For arbitrary H, a coordinate-space equivalence retaining all residual
   intertwining equations; actual-field transport through supplied identifications.
6. Focused/full builds, strict transitive axiom/import audit, layout and link
   checks, plus exact finite sign/rank controls with documented limitations.

Completion requires both literal contraction agreement and completeness.
Matching a rank or count alone does not meet this endpoint.

## Completed Work And Boundaries

- The v2 PDF appendix D.9 (PDF page 50) has been visually inspected. Its
  three flavor symmetry labels accompany the same local contraction. See
  [source recovery and dictionary](source-recovery.md).
- The adjacent-exchange dictionary is now explicitly conjugated to a
  symmetric component, an alternating component and a two-coordinate mixed
  component. A two-sided inverse connects this presentation to the independent
  physical exterior sector, without finite-dimensional assumptions.
- Nonredundant finite coordinates, both physical inverse identities, arbitrary
  H constraints and actual-field transport are proved. With trivial residual
  action the coordinate basis is independent and spanning; its general
  cardinality and three-generation dimension 57 are proved.
- The printed seed's actual raw exterior descent equals the completeness
  inverse. The source normalization `-T-U/3+V`, six-permutation reconstruction,
  exhaustiveness and candidate injectivity are proved. No acceptance obligation
  remains within this scope. General Li algorithms and package-specific arrays
  remain excluded, not implicitly certified.

## Result And Verification

The component relations are necessary and sufficient, not merely consequences
of exchange invariance. The mixed component reduces to one residual functional
symmetric in its last two Q inputs and with zero cyclic sum; its partner is
determined by swapping the first two inputs. Finite interpolation now gives a
physical coordinate equivalence. If Q has n flavors and L has m flavors, the
unrestricted dimension is
`m * (choose(n+2,3) + choose(n,3) + n*n-n + 2*choose(n,3))`.
The literal local-contraction bridge is proved; see the
[completed proof dossier](../../proof/current/applications/Physics/LI_QQQL_BASIS.md).

Planning verification: `node tools/docs/check-links.mjs` passed (391 Markdown
files, 2673 local links, zero errors); `git diff --check` passed.
No Lean build was rerun for the planning-only changes.

Component checkpoint: focused builds and the persistent component audit passed
(12 strict transitive axiom checks). `lake build` passed (6382 jobs), local
links passed (392 Markdown files, 2676 links, zero errors). The full build
replayed existing audit information; no new proof warnings were introduced.

Finite-coordinate checkpoint: `lake build` passed (6389 jobs) and the expanded
persistent audit passed 45 strict transitive checks. Layout passed (1062 modules),
local links passed (392 files, 2677 links) and `git diff --check` passed. No new
warnings remain. The printed local seed identity and its three nonzero
component projections are included in the audit.

Final verification: focused audit build passed (3297 jobs, 52 strict transitive
checks); `lake build` passed (6391 jobs). Layout passed (1064 modules), local
links passed (393 files, 2686 links, zero errors) and `git diff --check` passed.
The link checker required a read-only sandbox escalation for its Git subprocess.
No new Lean warnings were introduced. The user subsequently authorized master
integration. The verified proof endpoint is commit `checkpoint 01`; integration is
recorded by Git ancestry and the merge commit, not by a duplicated status field.

## References

- [Li et al., arXiv:2201.04639v2, including PDF appendices](https://arxiv.org/pdf/2201.04639v2)
- [Completed qque pilot](../li-basis-verification/README.md)
- [Qque proof dictionary](../../proof/current/applications/Physics/LI_QQUE_BASIS.md)
- [Four-family completeness and qqql starting point](../delta-l-one-completeness/README.md)
- [Derivative-free shared foundations](../derivative-free-completeness/README.md)
- [QqqlExteriorCompleteness](../../../Physics/StandardModel/Operators/QqqlExteriorCompleteness.lean)
- [QqqlExchange](../../../Physics/StandardModel/Operators/QqqlExchange.lean)
- [FourDoubletProductExchange](../../../Math/RepresentationTheory/Unitary/FourDoubletProductExchange.lean)
- [QqqlScalarFlavor](../../../Physics/StandardModel/Operators/QqqlScalarFlavor.lean)
