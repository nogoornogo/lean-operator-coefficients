# Reverse Placement: Small-Representation Feasibility

The [bounded plan](reverse-placement-plan.md) was executed. The subsequent
[Lean index certificate](lean-index-results.md) now proves the finite profile
system inconsistent; the character-to-physical-model bridge remains conditional. The
[exact character script](../../../tools/su6-light-placement-search/check_small_branching.py)
constructs complete standard SM torus characters for 1,6,15,20,21,35,70 and
conjugates, then subtracts complete SU(3)xSU(2)xU(1) irreducible characters.
This avoids identifying a color sextet or weak triplet with a target merely
because it contains one matching weight.

## Candidate component screen

| SU(6) formal character | Q copies | u^c copies | e^c copies |
| --- | --- | --- | --- |
| 1 | 0 | 0 | 0 |
| 6 | 0 | 0 | 0 |
| 15 = exterior square | 1 | 1 | 1 |
| 20 = exterior cube | 1 | 1 | 1 |
| 21 = symmetric square | 1 | 0 | 0 |
| 35 = 6 times bar6 minus singlet | 0 | 0 | 0 |
| 70 = 6 times exterior square minus exterior cube | 2 | 1 | 1 |
| bar70 | 1 | 1 | 0 |

The full blocks, including spectators and conjugates, are printed by the
script. Each decomposition reconstructs every original weight with its
multiplicity, and dimensions match the named formal characters. In particular,
21 and 70 provide different component profiles, so the previous single-ten
reasoning does not automatically exclude all of them. This is computational
character evidence, not new Lean continuous representation/branching equivalences.

## Necessary mass-pairing screen

For a residual-invariant bilinear mass commuting with the standard SM action,
a massive component R at Z5 charge q pairs with conjugate R at charge -q.
Thus the charge-resolved chiral difference
`n(R,q)-n(conjugate R,-q)` cannot be removed by such pairings. This necessary
index test does not assert that all permitted pairs actually acquire mass,
or that an index identifies a full light spectrum.

Construct one column of this index for each of the seven characters at each
of five scalar copy charges. These 35 columns admit arbitrary rational
linear combinations as a relaxation of physical nonnegative integer copy
numbers. Conjugate columns are already included in this span because the
conjugate character at q has the negative column of the original at -q.

Require the desired light spectrum to have exactly one Q,u^c,d^c,L,e^c with
the charges of each of the five normalized Z5 representatives, and no
additional charge-resolved chiral content. Exact Fraction elimination gives
coefficient rank 24 and an inconsistent augmented system for **every**
representative. The neutral standard-SM index is a positive control:
it equals the neutral fifteen column minus twice the neutral six column.

Consequently, even the rational relaxation cannot realize these five target
indices within the chosen representation pool and uniform scalar copy charges.
No number of extra copies from that pool fixes this necessary condition.
This is a bounded computational obstruction, not a Lean theorem classifying
SU(6) models. It presupposes the stated mass pairing and residual-charge
interpretation; the script does not certify a UV Yukawa or mass radical.

## Lean profile lemma

[ChargeProfileObstruction](../../../GUT/SU6/SelectionRules/Models/ChargeProfileObstruction.lean)
separately proves that equal singleton charge profiles force equal species
charges, hence neutral qque. Its application requires an actual charge-resolved
index and exact-light bridge; neither a UV character nor radical inclusion
alone supplies this premise. This generic lemma does not certify the larger
35-column computational system.

## Assessment and boundary

Adding the simplest complete multiplets does not presently yield a viable
realization of the selected Z5 request with only the specified SM chiral
content. Looking only at the attractive Q in 21, or U in bar70, would miss
the spectator/index obstruction. A larger/different representation pool,
non-scalar copy action or changed embedding remains untested. Additional
vectorlike light pairs do not change this index; additional chiral light
content changes the target and requires a new explicit spectrum decision.
Multiple generations, anomalies, symmetry-breaking mass terms, a scalar
potential and phenomenology are not inferred from this one-generation screen.

The intended result is a feasibility stop: there is no supported small-model
recommendation within this pool. New continuous representations, their actual
radicals or unrestricted representation searches are not silently initiated.

## Subsequent certificate

The [Lean certificate](lean-index-results.md) supersedes the computational-only
status of the matrix inconsistency. It does not promote the computational
branching dictionary into continuous representation equivalences or prove
actual mass/radical admission for a new physical model.

## Subsequent actual-mass connection

The [actual radical-index result](physical-index-results.md) independently
excludes these targets for arbitrary actual unitary SU(6) times commuting
residual actions on the standard embedding. It derives the obstruction
from the actual mass radical via the standard SU(5) chain, without using
the finite matrix admission premise. The individual branching equivalences
remain separate; noncommuting residual actions are not covered.
