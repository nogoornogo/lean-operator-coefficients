# Constraints on model inputs

Read the [general coefficient criteria](GENERAL_THEOREMS.md) as necessary
conditions on a model intended to forbid selected interactions. This organizes
input checks; it does not construct or classify all UV models.

## From prohibition to necessary conditions

For a specified selected domain, the decomposition gives

$$
\mathcal C_{\mathrm{selected}}=0
\iff\forall c\in\mathrm{selected},\quad\mathrm{Hom}_H(Q_c,\mathbb C)=0.
$$

The general [input interface](inputs/Math/PROHIBITION_INPUT.md) packages
these requirements. On semisimple sources they can be expressed by absence
of a common irreducible constituent with the trivial target. Scalar-action
criteria require actual action identities and a nontrivial carrier; labels
alone or constituent overlap before statistics do not decide qque support.

For the fixed cyclic SM dictionary, [structural classification](DECIDABLE_CLASSIFICATIONS.md)
turns absolute B1 prohibition into a finite necessary-and-sufficient condition:

$$
\forall L\in\{-17,-15,\ldots,17\},\qquad3q+Ll\not\equiv0\pmod{k}.
$$

More general residual actions, charged Higgs and prescribed LFV transitions
must use their own certified domains.

## Combined requests and mass constraints

A specification can combine B1, B2 and L2 prohibition or allowance; LFV has
separate transition selectors. Every allowed target requires its own actual
nonzero witness. Necessary conditions can be pulled back through certified
field and symmetry maps and composed with mass/kernel and copy-surplus
constraints. Those constraints retain their own hypotheses: a branching
match or a neutral character does not identify a complete light mass radical.

See [composable specifications](core/Math/COMPOSABLE_PROHIBITION_SPECIFICATIONS.md),
[pattern catalogue](../../topics/prohibition-patterns/catalogue.md),
[theorem-driven constraints](../../topics/theorem-driven-protection-constraints/README.md),
and [copy-surplus light inputs](inputs/Math/SPECIES_COPY_SURPLUS.md).

For the specified SU(5)-labelled $10,\overline5,40,50$ family and its
algebraic duals, the full-SM restriction admits a symmetric SM-invariant mass
with radical equivariant to $N$ SM generations exactly when

$$
(p_0-q_0,p_1-q_1,p_2-q_2,p_3-q_3)=(N,N,0,0).
$$

Here $p_i,q_i$ count the named representations and their duals. This is
existence of some suitable mass, not a claim about every invariant mass or an
SU(5)-invariant UV realization. See the
[exact copy-condition result](../../topics/prohibition-converse-boundaries/copy-mass-results.md)
for the dictionary, theorem source and counterexample to the every-mass reading.

## Converse boundaries and constructed inputs

A necessary filter becomes sufficient only when actual fields, actions,
statistics and coefficient witnesses have been connected on the same domain.
The [converse-boundary dossier](applications/Physics/PROHIBITION_CONVERSE_BOUNDARIES.md)
records successful bounded converse results and counterexample controls.

The [inverse cyclic construction](applications/Physics/INVERSE_CYCLIC_SM_CONSTRUCTION.md)
starts from finite charge filters and constructs an algebraic light/mass input.
Its lepton-parity example combines named SM fields, a spectator mass radical,
allowed charged-fermion Yukawa coefficients and all-degree derivative-free B1
prohibition. A simple-group UV lift, anomaly freedom and quantum exactness
remain unestablished. See the [model study](../../model-studies/inverse-cyclic-sm/README.md).

For other model dictionaries, use the [model-input guide](APPLICATION_GUIDE.md)
to distinguish a proved contradiction, an unsatisfied supplied premise and a
successful conditional application.

## Literature context for reverse constraints

[Koren (2022)](https://arxiv.org/abs/2204.01741v2) and
[Dreiner–Luhn–Thormeier (2006)](https://arxiv.org/abs/hep-ph/0512163v1) are
relevant symmetry/selection references. The former has an existing all-degree
algebraic [SM consumer](../../topics/koren-sm-selection/README.md); the latter
provides context for the [component-field study](../../model-studies/discrete-baryon-protection/README.md).
Their quantum/anomaly or MSSM assumptions do not follow from the generic
input constraints. Source locations and bounded claims belong to the
[model coverage ledger](../../verification/proton-protection-model-coverage.md).

The [literature map](../RELATED_LITERATURE.md) also links flavor-dependent
minimum-dimension work; it does not establish a converse or a UV realization.
