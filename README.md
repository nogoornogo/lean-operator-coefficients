# Algebraic Operator Coefficients and Symmetry Criteria in Lean4

## Overview

A Lean formalization of derivative-free operator coefficients, symmetry
selection rules and their applications to specified field and model inputs.
The project connects general algebraic theorems with exact structural tests
and conditional model checks. Allowed coefficients do not by themselves
establish generated interactions or decay rates.

## General Theorems

Coefficient extraction and reconstruction identify invariant coefficients with
residual intertwiner spaces, at every degree:

$$
\mathcal C_{n,m}^{G\times H}
\simeq \prod_{c\in\mathrm{Content}(n,m)}\mathrm{Hom}_H(Q_c,\mathbb C).
$$

Symmetry extension is characterized by surjectivity of restriction:

$$
\mathcal C^K=\mathrm{res}_{H\to K}(\mathcal C^H)
\quad\Longleftrightarrow\quad
\mathrm{res}_{H\to K}\text{ is surjective}.
$$

All-degree charge selection rules also force invariant coefficients to vanish
when an actual symmetry element acts on their domain by a scalar other than one.

[General theorems, definitions and assumptions](docs/proof/current/GENERAL_THEOREMS.md).

## Finite Structural Classifications

For the fixed three-generation SM/Higgs input with scalar cyclic q/l actions,
all-degree coefficient existence reduces to finite structural conditions.
In particular, absolute $\Delta B=1$ allowance has the exact charge criterion

$$
\mathcal C_{|\Delta B|=1}\ne0
\quad\Longleftrightarrow\quad
\exists L\in\{-17,-15,\ldots,17\},\quad 3q+Ll\equiv0\pmod{k}.
$$

Here $k$ is the cyclic group order, $q,l$ are the quark and lepton charges
modulo $k$, and $L$ is the normalized lepton-number change.

The certified 572-input domain is $2\le k\le12$, $0\le q,l<k$, with
$3q+l\not\equiv0\pmod{k}$, excluding inputs that already allow dimension-six
QQQL coefficients. All 326 allowed cases in this domain have exact minimum
engineering dimensions **among derivative-free coefficients**; the remaining
246 inputs are forbidden at all degrees in that domain.

[Structural classifications and minimum-dimension scope](docs/proof/current/DECIDABLE_CLASSIFICATIONS.md).

## Constraints on Model Inputs

The coefficient criteria can be read backwards: a requested prohibition
imposes necessary conditions on the supplied fields, symmetry and mass data.
For example, in the specified SU(5)-labelled $10,\overline5,40,50$ family
and its algebraic duals, existence of an SM-invariant symmetric mass with
exactly $N$ SM generations as its radical requires the net-copy condition

$$
(p_0-q_0,p_1-q_1,p_2-q_2,p_3-q_3)=(N,N,0,0).
$$

Within that fixed SM-restricted family the condition is also sufficient for
existence of some such mass; it does not construct an SU(5)-invariant UV mass.

[Input constraints, converse boundaries and construction examples](docs/proof/current/INPUT_CONSTRAINTS.md).

[Combined allowance/prohibition patterns for B1, B2, L2 and prescribed LFV](docs/topics/prohibition-patterns/catalogue.md).

## Concrete Model Inputs

Specified cyclic and nonabelian actions provide concrete tests. The $S_3$
flavor sample has an actual nonzero qque coefficient:

$$
\mathcal C_{\mathrm{qque}}^{\mathrm{SM}\times S_3}\ne0.
$$

Ten candidate model groups have been checked with their model-to-input
premises and unresolved conditions recorded separately.

[Model inputs, examples and application procedure](docs/proof/current/APPLICATION_GUIDE.md).

## Independent Proofs and Exploration Results

Reusable results from earlier investigations include branching and chirality
certificates, specified stabilizers and Takagi factorization of a complex
symmetric matrix:

$$
U^{T}MU=\mathrm{diag}(\sigma_1,\ldots,\sigma_n),
\qquad U^\dagger U=I,\quad \sigma_i\ge0.
$$

[Independent results and their individual boundaries](docs/proof/current/RETAINED_RESULTS.md).


## Literature and Comparison Findings

The [related literature and references](docs/proof/RELATED_LITERATURE.md)
map published work to the project’s results and their stated scope.
The [literature comparison findings](docs/verification/literature-findings.md)
summarize three formal comparisons: a printed-basis applicability boundary,
a normalization discrepancy under fixed definitions, and a conditional
coefficient mismatch, with assumptions and unresolved limits recorded separately.

## Development Approach

Formalization was carried out primarily with Codex (GPT-6 Astra and GPT-6.1
Sol), with reviews using Claude Code and ChatGPT at selected stages. The
[workflow](docs/architecture/WORKFLOW.md) and
[Lean tooling guide](docs/architecture/LEAN_TOOLING.md) describe the current
practices. These practices evolved during the project; the architecture
documentation is not a retrospective description of every stage.

## Build

See [build instructions](docs/architecture/BUILD.md).

## How the Project Developed

The project began with an LLM-assisted discussion of whether a specified
SU(6) model could protect proton stability by forbidding $\Delta B=1$
operators. The discussion led to the opposite conclusion under the proposed
assumptions. Formalizing that argument in Lean with Codex became the starting
point of this repository. The resulting no-go statements concern specified
model and symmetry classes; they do not exclude every SU(6) construction.

Making those assumptions precise required distinguishing chiral indices from
actual massless fields, and symmetry-allowed coefficients from interactions
generated by heavy-field exchange. Work on branching, mass kernels and
residual actions then led from individual nonzero operator witnesses to
necessary and sufficient conditions for entire coefficient spaces. Related
operator sectors exposed common algebraic structures, which became the
general derivative-free completeness and selection-rule theorems above.

The later work applied those theorems to fixed SM/Higgs inputs: finite support
tests, exact minimum dimensions in a specified cyclic domain, and conditional
checks of concrete model inputs. Comparisons with published expressions also
produced the [literature comparison findings](docs/verification/literature-findings.md). The original model-search question
thus grew into a framework for stating assumptions explicitly and checking
what follows from them. No protecting SU(6) model was established by the
investigated routes; broader constructions remain outside their scope.

See the [research trajectory](docs/topics/proof-program-context/RESEARCH_TRAJECTORY.md)
and [SU(6) exploration boundary](docs/topics/sm-support-and-lfv-decomposition/su6-exploration-closure.md)
for the underlying records and qualifications.

## Project Context and Limitations

This is an individual project motivated by personal interest, developed with
LLM assistance by an author who is not a theoretical physicist. The author
does not claim complete understanding of all mathematical and physical
assumptions or of every statement formalized here, and cannot independently
vouch for their correctness or physical relevance.

Lean checks proofs of the encoded statements relative to their definitions,
explicit hypotheses and foundational axioms. This does not by itself validate
the physical assumptions, establish correspondence with a published model,
or ensure that an informal explanation accurately describes the formal result.
LLM-assisted reviews provide additional scrutiny but may share errors and are
not a substitute for independent expert assessment. Readers should inspect
the formal statements and their documented scope when using these results.

The formal results do not include RGE evolution, nonperturbative QCD,
hadronic matrix elements or lattice calculations; see the
[physical interpretation and exclusions](docs/proof/current/inputs/Physics/assumptions/physical-scope.md#physical-interpretation-and-exclusions).

## License

[Apache License 2.0](LICENSE). Third-party material retains its own licenses
and attribution requirements.
