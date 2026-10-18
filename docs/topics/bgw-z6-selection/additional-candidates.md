# Additional Non-Supersymmetric Candidates

Source preflight, stage 01. The user requested another non-supersymmetric
example after the completed BGW certificate. These are proposed applications,
not additional Lean results. No new proof branch or master integration is
authorized by this record.

## Recommended: Koren's Standard-Model Symmetry

Seth Koren, *A Note on Proton Stability in the Standard Model*,
[arXiv:2204.01741v2](https://arxiv.org/abs/2204.01741v2),
[PDF](https://arxiv.org/pdf/2204.01741v2),
[publication](https://doi.org/10.3390/universe8060308).
Inspected Table I and pp. 2–3, especially the symmetry product and the final
two conservation conditions. Table I uses B=3 B_usual and Y=6 Y_usual.

For three colors and three generations the proposed residual symmetry is
U(1)_(3B_usual-3L) times Z3^L. In the repository dictionary write b=3B_usual,
l=L. Its invariant supports obey b-3l=0 and l=0 modulo 3. Algebraically these
imply 9 divides b: absolute B_usual=1,2 and absolute L=2 are simultaneously
excluded. This implication is our adapter inference, not a checked theorem.
Unlike BGW, this symmetry forbids LLHH. It preserves no general LFV prohibition.

Proposed bounded endpoint: construct actual scalar actions on the existing
signed SM/Higgs modules, prove detection for the union
abs(b)=3 or abs(b)=6 or abs(l)=2, and use ComposableBLSupport.forbidden
to transport prohibition to the existing coefficient decomposition. Check the
source declaration name before implementation. Higgs charges are zero.
No new field alphabet is expected. Keep the physical three-generation condition
separate from any algebraic theorem valid on arbitrary copy modules.

Anomaly freedom and quantum survival are literature justification, not proved
by an invariant-coefficient theorem. Stop before instantons, amplitudes,
hadronic states, rates, or a full-paper certificate. A symmetry-respecting EFT
is an explicit condition; arbitrary SM-gauge-invariant higher operators need
not preserve this extra symmetry.

## Alternative: Davighi–Greljo–Thomsen

*Leptoquarks with Exactly Stable Protons*,
[arXiv:2202.05275v2](https://arxiv.org/abs/2202.05275v2),
[PDF](https://arxiv.org/pdf/2202.05275v2),
[publication](https://doi.org/10.1016/j.physletb.2022.137310).
Inspected the abstract, Sec. II, Table I and Eqs. (2)–(4).

This is a non-supersymmetric extension with scalar leptoquarks, right-handed
neutrinos and symmetry-breaking singlets. It combines residual baryon
protection with flavor restrictions. The abstract's all-order baryon protection
must not be conflated with the renormalizable flavor restriction in Sec. II.
Neither all-degree LFV prohibition nor L=2 prohibition is established by this
preflight. Its full field alphabet and family-dependent actions would require
more adapters than the Koren SM restriction. Neutrino mass generation and
flavor phenomenology are outside the proposed symbolic endpoint.

## Decision And Verification

Recommend Koren first for a genuinely different three-target regression of the
composable prohibition interface. Defer the leptoquark extension. This preflight
stops at source and adapter assessment; implementing an independent proof topic
requires the repository's explicit top-level branch direction. Sources are
pinned above. Documentation checks are recorded after completion; no Lean
build was rerun because no proof or theorem premise has changed.
`node tools/docs/check-links.mjs` passed (640 Markdown files, 3986 local links,
91 heading fragments, zero errors); `git diff --check` passed.
