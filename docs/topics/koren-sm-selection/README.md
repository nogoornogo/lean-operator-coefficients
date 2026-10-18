# Koren SM Symmetry: Three Simultaneous Prohibitions

- Status: completed; sufficient finite-subgroup prohibition proved
- Working branch: `proof/koren-sm-selection`
- Integration target: `master`; merge requires separate authorization
- Authorization: user requested verification of the recommended Koren candidate

## Frozen Contract

Use the existing signed SM fermions and Higgs/opposite species. With b=3B_usual
and l=L, construct the Z9 times Z3 subgroup action with charges (b-3l,l).
Explicitly identify its embedding into Circle times Z3, the algebraic carrier
of the paper's U(1)_(B_paper-3L) times Z3^L. Prove character detection and
all-degree derivative-free prohibition for abs(b)=3 or abs(b)=6 or abs(l)=2.
Connect actual coefficient inputs and their residual decomposition through
ComposableBLSupport. Keep arbitrary complex copy modules in the algebraic
statement; the literature interpretation assumes three physical generations.

The finite subgroup is sufficient for these prohibitions; it does not impose
the full continuous charge conservation or characterize all allowed supports.
Stop before anomaly/quantum-survival proofs, instantons, matching, masses,
amplitudes, rates, derivatives and EOM/IBP. No custom axioms or new dependencies.
Acceptance: focused build, persistent strict axiom audit, full build, layout,
documentation-link and diff checks, statement/assumption review and commit.

## Sources

Seth Koren, *A Note on Proton Stability in the Standard Model*,
[arXiv:2204.01741v2](https://arxiv.org/abs/2204.01741v2),
[PDF](https://arxiv.org/pdf/2204.01741v2),
[publication](https://doi.org/10.3390/universe8060308).
Table I fixes B_paper=3B_usual and Y_paper=6Y_usual. Pages 2–3 give the
continuous/discrete symmetry product and final paired conservation conditions.
These motivate the constructed action; anomaly and quantum arguments remain
outside the certificate. This is an EFT conditioned on the extra symmetry,
not a statement about every SM-gauge-invariant EFT.

## Outcome

The frozen endpoint is proved: actual representations, injective subgroup
embedding, character restriction and detection feed the existing composable
interface. Absolute B1/B2/L2 coefficients and residual factors vanish at every
derivative-free degree. See [results](results.md) and [verification](verification.md).
No remaining work inside this endpoint. Merged into master by `checkpoint 01`
at stage 01; BGW integration follows in `checkpoint 02`.

## Further Candidate Preflight

The requested [additional example assessment](further-examples.md) recommends
a bounded UV/residual flavor comparison in a non-supersymmetric leptoquark
model, with lepton quarticity as an alternative. These are independent
proposals, not extensions of the completed theorem. Documentation-only checks
are recorded after source assessment; no Lean build was rerun for this record.
`node tools/docs/check-links.mjs` passed (639 Markdown files, 3982 local links,
91 heading fragments, zero errors); `git diff --check` passed.
