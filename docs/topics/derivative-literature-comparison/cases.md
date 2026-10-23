# Six Finite Comparison Cases

This file preserves the frozen targets. Numerical values below are
**literature expectations**; the [results](results.md) distinguish proved
subsets, supplementary diagnostics and unproved claims. Source IDs refer to the [pinned register](references.md).
The [common gates](plan.md) and queue advancement apply to every case.
Effort labels describe implementation risk, not calendar estimates.

## C1 — One-Dimensional Scalar EOM And IBP

**Source:** R1, especially Eq. (3.11).
**Effort:** small to medium; the one-species quadratic IBP control already
exists, but the two-species multidegree presentation still needs a bridge.

Freeze one derivative direction and one or two commuting species. The free
equations are the second derivative of each species, with all descendants
and products included. First compare the one-species two-field, two-derivative
source before and after EOM: expected dimensions are 1 for IBP alone and 0
for EOM plus IBP. This prevents conflating off-shell and on-shell inputs.

For two species select multiplicities (1,1) and (2,2), derivative degrees
0, 1 and 2. The generating function predicts respectively (1,1,0) and
(1,1,1). Construct the actual finite quotients, separating probes and inverse
coefficient maps. Test degree-zero compatibility with the nonderivative
source before imposing EOM. An optional bounded momentum-slot dictionary
must be proved if used; no Fourier or all-orders series theorem is needed.

Success is a complete certificate for these finite sectors, through the
public input operations and actual linear-EOM bridge. A mere expansion of
the rational generating function does not count. At any local terminal
outcome record the proven subset or missing multidegree bridge and go to C2.

## C2 — Four Identical Scalars With Actual Lorentz Symmetry

**Source:** R2, Section 6.1, Eq. (6.3).
**Effort:** medium to high; the new risk is invariant completeness, not
ordinary scalar derivatives.

Freeze one commuting scalar species, four spacetime directions, field
count four, free massless equation and derivative degrees 0, 2 and 4.
Compare the expected coefficient dimensions (1,0,1). The four-derivative
candidate is the metric contraction of four first derivatives, conventionally
written as the square of the scalar kinetic contraction.

Prove its dictionary to the actual complex Lorentz action and state the
change from the paper's Euclidean metric convention. Prove the complete
invariant coefficient space of the actual EOM/IBP quotient, with extraction,
reconstruction and a nonzero separating probe at degree four. Degree two
must vanish for the stated relations, while degree zero recovers the old
input. Do not replace actual Lorentz invariance by a guessed contraction list.

Try structural metric contractions, then a bounded complete finite test/rank
presentation if needed. Neither route may assume invariant-quotient
commutation. If the invariant-span proof is unavailable, retain any literal
relation/nonzero result with that limit, record gap G1 and advance to C3.

## C3 — Higgs Relation Across Field Counts

**Source:** R3, Table 2 and Eq. (5.3).
**Effort:** medium to high; a Higgs/conjugation dictionary and full-source
relation image are needed, even though the target is one relation.

Freeze a complex weak doublet H with independent polynomial H and conjugate
labels, the actual dual/conjugation dictionary, Lorentz symmetry and global
weak/hypercharge actions. Gauge and Yukawa couplings are zero. Let
rho = H-dagger H. Fix the leading density

\[
L_0=(\partial_\mu H)^\dagger\partial^\mu H
       -a\rho-\tfrac b2\rho^2,\qquad a,b\in\mathbb R.
\]

Coefficients are complex, with a,b cast into them. This chosen potential
normalization must be mapped explicitly to the paper's signs and couplings.
Generate the equations of L0 with the helper and independently identify
their differential ideal with the direct leading-equation input. Every
component and its formal conjugate is varied. The higher-dimension
operators are probes; do not generate the quotient from their own Euler
equations.

Define literal versions of the two Table 2 derivative operators and the
redundant expression rho times the Higgs kinetic contraction. Derive the
exact identity in the full EOM/IBP source. For the chosen L0 the proposed
relation to prove is

\[
[\rho(\partial H)^\dagger\partial H]
 =\tfrac12[\rho\Box\rho]+a[\rho^2]+b[\rho^3].
\]

Check the identity's current and normalization, not just class labels.
Use `.select` on a stable finite span containing these representatives and
the two displayed derivative candidates, retaining its full relation
preimage. Show how a global coefficient evaluates this relation and how the
same selected operations extract/reconstruct its values. Include a nonzero
potential-coupling control so a discarded cross-count term is detected.

Success here means the literal input and relation certificate, including
helper/direct agreement. Independence/completeness of the two-candidate
derivative basis is an additional claim only if proved; it is not presumed
by this relation contract. No full gauged/Yukawa Warsaw result is requested.
Record any missing Higgs dictionary as G2, any full-relation-image gap as G3,
then proceed to C4 at the local stop.

## C4 — The Three Higgs Four-Derivative Candidates

**Source:** R4, Table 2.
**Effort:** high; bounded finite local invariant completeness is the main
uncertainty. A general invariant solver is outside scope.

Freeze H, its dual and actual Lorentz/global weak/hypercharge actions as in
C3, but use **free massless linear equations** for this case. Test exactly
two H factors, two conjugate factors and four ordinary derivatives. This
is an explicit gaugeless, free specialization of the displayed class, not
an assumption that the full covariant SMEFT quotient splits into this class.

Transcribe the three contractions with the exact index order of the pinned
Table 2. Prove their actual-source interpretation, invariance, EOM/IBP
descent and separating probes. Target an actual three-coordinate coefficient
equivalence with both inverse laws, not just three nonzero expressions or
an independently printed count of three. Retain the source-to-coordinate
relation transport if using `FiniteLocalExtraRelations`.

Reuse a C3 dictionary only if it was proved. C3 stopping does not cancel this
case: independently test the available literal candidates and the G2 gate.
If the complete invariant span cannot be established within the two routes,
retain the narrower checked input/relation result, record G1/G2 as applicable
and move to C5. No additional dimension-eight classes are added here.

## C5 — A Genuine Mixed Weyl/Higgs Derivative Current

**Sources:** R5, Eqs. (4.23)–(4.26); R4, Table 5 as a second notation.
**Effort:** medium to high; the derivative degree is small, but chirality,
odd-field signs and the actual invariant dictionary are essential.

Freeze one charged-lepton flavor and its charge-conjugate/conjugate Weyl
labels, two H and two conjugate H factors, one derivative. Use the actual
paired Weyl and scalar representations and their free massless linear
equations, with gauge/Yukawa couplings zero. The source has two odd factors
and four even factors. It is not the already-vanishing single-odd-field
IBP example.

The literal target is the charge-conjugate lepton current contracted with
the Higgs bidirectional derivative current, multiplied by rho, including
the displayed factor of i. Fix odd-field order, sigma matrices, conjugation
and the definition of the bidirectional derivative. Prove the two-/four-
component translation before comparing it with Murphy's charged-lepton
current. Do not silently identify physical dagger or charge conjugation
with an unproved abstract linear map.

Establish actual mixed EOM/IBP descent and test extraction/reconstruction
with the literal expression. Target the one-coordinate complex coefficient
space of this fixed content; any Hermitian real-count statement needs its
own adjoint/reality proof. Include an odd-field reorder sign control and
an IBP relation moving the derivative between the Higgs factors. Prove
completeness independently if reporting agreement with the single displayed
type. A current-translation identity alone is a narrower result.

Use [paired equations](../../../Physics/FieldTheory/Jets/ConjugateWeylEquation.lean)
and the [jet adjoint](../../../Physics/FieldTheory/Jets/WeylJetAdjoint.lean)
where their hypotheses match. If C4 stopped, still run this case's own gate;
it does not depend on C4's rank certificate. Record G1/G2/G4 as appropriate,
then go to C6. Additional flavors and other derivative classes are excluded.

## C6 — Actual Substitution And The First-Order Boundary

**Source:** R6, Section 3, Eq. (3.2).
**Effort:** small to medium; actual scalar substitution and first variation
already exist. This case is independent of the Higgs/Weyl dictionaries.

Construct a scalar polynomial example with the actual Lorentz metric,

\[
L_0=\tfrac12\partial_\mu\phi\,\partial^\mu\phi
      -\tfrac g4\phi^4,\qquad
\phi\longmapsto\phi+\varepsilon\phi^3.
\]

This is a chosen specialization of the paper's formula, not a claim to
transcribe a particular worked example. Use actual jet-compatible polynomial
substitution; prove coefficient zero is L0 and coefficient one is the
helper's Euler expression times phi cubed plus its explicit divergence.
Identify its direct-equation and helper-generated input evaluations on the
same leading L0, with the same source/action/relations.

Retain the second coefficient and check a raw nonzero specialization, for
example at g=0 by an exact evaluation of phi and its first jets. Do not
claim this raw coefficient is nonzero modulo EOM/IBP, or that it disproves
all-order field-redefinition equivalence. The control detects loss of higher
terms in a first-order computation, which is the intended boundary.

Success is this exact finite polynomial/substitution certificate through
order two and the first-order input agreement. No analytic action,
Jacobian or quantum equivalence is required. Record any unproved substitution
bridge as G5. At its local stop, finish the portfolio report only after
checking that C1–C5 also have terminal outcomes.
