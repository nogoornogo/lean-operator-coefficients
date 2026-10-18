# Scoped findings from literature comparisons

Formal comparisons of published operator expressions and model inputs exposed
three kinds of issues: an exact applicability boundary for a printed basis,
a local normalization discrepancy under fixed definitions, and a conditional
coefficient mismatch. Each entry records the source, mathematical consequence,
convention assumptions and unresolved scope.

These are scoped comparison results, not three unconditional paper-error
certificates. This page summarizes the existing proofs and evidence; it does
not establish whole-paper verification or phenomenological consequences.

## Overview

| Source and location | Finding | Established scope and limit | Evidence |
| --- | --- | --- | --- |
| **F1.** [Li et al., 2007.07899v1](https://arxiv.org/abs/2007.07899v1), Eq. (5.63), PDF p. 46 | The ten printed seed orbits span dimension 24 in a 25-dimensional selected local six-quark invariant space. The missing component and its physical flavor boundary are identified. | Actual printed-orbit completeness is proved for down-flavor dimension at most three; a four-down-flavor witness escapes it. No entire-paper counting-table or software-error claim. | [basis dossier](../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md), [flavor-boundary dossier](../proof/current/applications/Physics/LI_SIX_QUARK_FLAVOR_BOUNDARY.md) |
| **F2.** [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/abs/2211.02054v2), Eqs. (2), (10)–(14), (21), (24) | In the fixed canonical field/coupling/VEV reading, the displayed heavy entry has a square-root-of-two norm discrepancy and the displayed light ratio fails an exact mass-kernel test. | The local comparison survives nonzero common matrix factors and specified whole-multiplet scalar changes. It does not classify every field/kinetic convention or prove complete signed coefficient matching. | [local comparison](../topics/ps-bnv-coefficient-bridge/common-scale-result.md), [rescaling result](../topics/ps-bnv-coefficient-bridge/multiplet-rescaling-result.md) |
| **F3.** [Dev–Mohapatra, 1504.07196v2](https://arxiv.org/abs/1504.07196v2), Eqs. (1), (3), (4) and Fig. 1 | A supplied Hermitian action gives a coefficient differing from the displayed scalar in explicit dictionaries; exact compensating-normalization conditions and bounded obstructions are recorded. | Source adoption and the complete physical normalization dictionary remain conditional. Unrestricted rational/algebraic normalization exclusion and phenomenological consequences are not certified. | [Action/coefficient dossier](../proof/current/applications/Physics/DEV_MOHAPATRA_CONNECTION.md), [normalization closure](../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md), [magnitude obstruction](../topics/dev-mohapatra-coefficient-connection/review-closure-results.md) |

## F1 — Printed span and its flavor boundary

The implemented epsilon interpretation gives

$$
\dim V_{\mathrm{local}}=25,\qquad
\dim V_{\mathrm{printed}}=24,\qquad
V_{\mathrm{printed}}=\ker P.
$$

The missing probe descends to a functional on
$\mathrm{Sym}^2 U\otimes\Lambda^4 D$. For finite-dimensional D with
dimension at most three it vanishes, and the physical printed-Hom equivalence
is proved with all typed exchanges and residual equivariance retained. For
$U=\mathbb C$, $D=\mathbb C^4$ and trivial residual action, an actual exterior
witness lies outside the printed span.

The useful conclusion is an exact applicability boundary for this printed
presentation. It does not say that a physical three-generation SM operator
was omitted, nor that the paper's full counting polynomial is wrong.
Four-component C-matrix and hook-length normalization comparison remain
outside this certificate.

Evidence: [printed-span/flavor theorem and source map](../proof/current/applications/Physics/LI_SIX_QUARK_FLAVOR_BOUNDARY.md),
[bounded source coverage](li-basis-coverage.md), and
[original selected-basis result](../topics/li-six-quark-basis/results.md).

## F2 — Local normalization and light-kernel consistency

With the source reading and VEV definition held fixed, the documented entry
comparison has the form

$$
M_{\mathrm{read}}=\overline{y_R}\,v_R/\sqrt2,\qquad
M_{\mathrm{display}}=y_R v_R,\qquad
\lVert M_{\mathrm{display}}\rVert=\sqrt2\,\lVert M_{\mathrm{read}}\rVert.
$$

For nonzero coupling/VEV these norms differ. The exact zero-mu light-kernel
test also fails for the displayed mode under its stated nonzero conditions;
an overall nonzero matrix factor cannot fix it. Specified simultaneous
whole-multiplet scalar changes preserve the corresponding norm comparison.

This isolates a local consistency issue under explicit definitions. It does
not exhaust alternative coordinated field definitions or kinetic metrics,
prove all displayed effective coefficients wrong, or establish revised decay
rates or bounds. A change in the meaning of a VEV symbol is a possible source
reading, not a convention-equivalence theorem already proved here.

Evidence: [common-factor theorem](../topics/ps-bnv-coefficient-bridge/common-scale-result.md),
[whole-multiplet result](../topics/ps-bnv-coefficient-bridge/multiplet-rescaling-result.md),
[model explanation](../model-studies/pati-salam-protection/generated-coefficient.md),
and [source coverage](proton-protection-model-coverage.md).

## F3 — Conditional coefficient and normalization comparison

For a supplied derivative-free Hermitian action, exact all-degree elimination
and a nonzero literature-operator witness connect the action to the selected
six-quark coefficient. The [coefficient dossier](../proof/current/applications/Physics/DEV_MOHAPATRA_CONNECTION.md)
and [normalization closure](../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md)
record the source dictionary and explicit hypotheses. Within the stated
multiplier family the matching condition is

$$
-8\pi^2(ab)^2=t\mu^2\nu.
$$

Here $\mu,\nu$ identify scalar/Majorana mass parameters, $a,b$ identify the
selected vertices and $t$ identifies the comparison operator/action sign;
the original nonzero mass/coupling hypotheses remain. The canonical and
ordered-no-half dictionaries give coefficient ratios $-8\pi^2$ and
$-32\pi^2$. These are conditional action identities, not a certified assertion
that the paper is wrong by exactly $16\pi^2$.

Arbitrary unit phases and an explicit bounded magnitude-compensation family
are excluded by the [magnitude-obstruction results](../topics/dev-mohapatra-coefficient-connection/review-closure-results.md). Unrestricted rational or
algebraic compensation is not excluded. An adopted source-to-action dictionary
and physical matching remain separate from the algebraic calculation.

Evidence: [model explanation](../model-studies/dev-mohapatra/coefficient-evaluation.md),
[all-degree elimination](../topics/dev-mohapatra-coefficient-connection/heavy-elimination-results.md),
[normalization matching iff](../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md),
[phase and magnitude bounds](../topics/dev-mohapatra-coefficient-connection/review-closure-results.md),
and [source coverage](proton-protection-model-coverage.md).

## How to present the contribution

A supported description is: **formal comparison exposed an exact printed-span
applicability boundary, a fixed-reading normalization inconsistency, and a
conditional coefficient mismatch.** Each finding has a
source location, convention dictionary, explicit mathematical consequence and
stated unresolved scope.

Keep these findings distinct from bibliography-only relationships in the
[related-literature map](../proof/RELATED_LITERATURE.md). Author notification
and separate public errata/reporting remain separate decisions; no external
contact, paper-wide refutation or change to numerical phenomenology is asserted.
