# Literature assessment: the 107 neutral constant-content entries

Reviewed stage 01. This is a proposed proof plan, not a new rank theorem.
It refines the existing topic on `proof/sm-rank-certificates`; no implementation,
dependency change, merge or external-mathematics premise is introduced.

Implementation progress is recorded separately in the
[structural character milestone](structural-character-results.md). The user
has confirmed that numerical table output is acceptable as a consequence;
the acceptance requirement is on the structural proof, not its presentation.

The next algebraic connection uses a spanning property: the images of all
SL2 symmetric-power intertwiners span the representation. Prove closure under
tensor products using the existing SL2 Clebsch–Gordan surjection, and under
equivariant quotients. Apply this to iterated tensors and their exterior
quotients, then the actual L/Higgs source. This avoids requiring an explicit
list of irreducible multiplicities for the compact/complex comparison.
Acceptance still requires the actual-source instantiation, with no new
spanning hypothesis left on that source. The multiplicity/counting adapter
remains a distinct obligation after invariant preservation.

## Corrected prerequisite and endpoint

The CSV's unknown rows are Q: 48, conjugate Q: 48, L: 5, conjugate L: 6.
They contain only one species each. A general mixed-species dimension theorem
is **not necessary** to close these 107 entries. The constant-species dimension
and statistical exterior equivalence already exist. What is missing is the
dimension of the invariant coefficient space in these neutral cases.

Freeze three flavors, trivial residual group, the existing actual gauge and
paired Weyl actions, and the derivative-free Higgs constituents. Following
the user's structural-proof preference, the endpoint is a theorem uniform in
the degrees n, m and delta, identifying the actual invariant multiplicity by
a proved representation decomposition or symbolic character formula.
A total numerical classifier is an optional corollary, not the endpoint.
Rank-nullity then gives

    rank = choose(dimension(s), n) * (m + 1) - invariantDimension.

Do not infer mixed-content completeness, q/l selection or the 572-assignment
classification. Do not equate ordinary zero-weight dimension with invariants.

## Structural proof preference

Fixed-degree L proofs are permitted as provisional research milestones and
tests of the interfaces. A kernel-checked individual theorem is still an
unconditional proof of its stated case; "provisional" describes its role in
the larger project, not a weakened trust boundary or an assumed lemma.

The final argument must not consist of dispatching each degree to a table
entry or a separate numerical rank certificate. Keep degrees symbolic in
the character, decomposition, equivariance and dimension arguments. A finite
sum/product indexed by weights or partitions is acceptable as a structural
formula when its equality with the actual invariant dimension is proved
uniformly, without specializing degrees and evaluating each case. Merely
wrapping exhaustive case evaluation in a universally quantified statement
does not meet this endpoint. Explain the resulting support criterion too;
an unevaluated kernel dimension is not a new multiplicity formula.

Keep the flavor count fixed at three unless a further generalization is
explicitly adopted. The structural goal does not silently enlarge physical
scope. Numerical tables remain derived examples and regression evidence.

## Mathematical and physical references

1. Etingof et al., *Introduction to Representation Theory*, section 2.11,
   exercise on symmetric/exterior powers and their traces,
   [author-hosted book](https://math.mit.edu/~etingof/representationtheorybook.pdf).
   Exterior basis elements correspond to subsets of basis indices; weights
   add and multiplicities count subsets. This motivates a finite integer
   recurrence, not enumeration of a dense constraint matrix.
2. Peter Woit, *The Weyl Character Formula*, sections 2–3, Theorem 2,
   [lecture notes](https://www.math.columbia.edu/~woit/LieGroups-2012/weylcharacter.pdf).
   Weyl integration/character formulas extract irreducible multiplicities.
   Their consequence proposed here is constant-term extraction against the
   positive-root denominator. The notes outline the proof; citation is not
   a replacement for proving the required A1/A2 instance in Lean.
3. Nazarov, Postnova and Scrimshaw, *Skew Howe duality and limit shapes of
   Young diagrams*, sections 2.2 and 4.1,
   [paper](https://arxiv.org/pdf/2111.12426).
   Skew Cauchy/Howe decomposes an exterior power of a tensor product into
   Schur functors indexed by transposed partitions. This offers structural
   cross-checks and possible small-sector proofs. It does not directly solve
   the restriction of the Q multiplicity space to weak, Weyl and flavor
   factors; that branching problem must still be handled.
4. Criado, *BasisGen*, sections 2.1–2.2,
   [paper](https://arxiv.org/pdf/1901.03501).
   Describes integer weight arithmetic, exterior/symmetric-power weights,
   and singlet extraction for field contents. Use only its derivative-free
   representation-counting guidance. Its Lorentz Lie-algebra convention
   requires a separate comparison with the repository's actual group.
5. Lehman and Martin, *Hilbert Series for Constructing Lagrangians*,
   [paper](https://arxiv.org/pdf/1503.07537).
   Fermionic/bosonic generating functions and invariant projection provide
   a second description of the same counting problem. A Hilbert-series
   number or software result is diagnostic evidence, not a Lean premise.

## Route A: finite characters and multiplicity extraction (preferred)

For a species with torus basis weights w_i, define a finite Laurent polynomial

    E_s(t,x) = product_i (1 + t*x^(w_i)).

Repeated weights retain their distinct basis indices, including three flavor
copies. The coefficient of t^n is the character of the exterior source.
Multiply by the Higgs character sum_{j=0}^m z^(m-2*j). Hypercharge neutrality
is handled separately using the already proved charge formula.

For the semisimple factors, the proposed extraction is

    invariantDimension = CT(character * product_{positive roots a}(1-x^(-a))).

This one-sided denominator uses Weyl invariance of a genuine character; do
not add the full-root denominator without its Weyl-group normalization.
For A1 the corresponding multiplicity identity is weight(0)-weight(2).
For Q the factors are A2 color and two A1 factors (weak and its single Weyl
chirality). L has the two A1 factors only.

Required new proofs, in order:

1. A finite weight recurrence equals the character of the actual exterior
   source. Reuse `ConstantPatternExterior`, and the pinned TauCeti
   `exteriorPower.map_basis_exteriorPower_of_apply_basis` and
   `exteriorPower.trace_map_of_apply_basis`. Prove the Higgs character adapter.
2. For these single-chirality polynomial representations, prove equality of
   invariants under the actual Weyl group and the compact/algebraic action
   used for character extraction. Conjugate chirality needs its own transport.
   Restricting a mixed-chirality representation to one diagonal SU(2) would
   be invalid as a general replacement and is not proposed.
3. Prove the A1 extraction instance on the generated representations; use
   existing SU2 Clebsch–Gordan as support, not as an assumed classification
   of every representation. Prove a degree-uniform formula for L/conjugate-L.
   Fixed-degree proofs, including reproduction of LLHH nullity 6, are
   provisional milestones toward that formula, not completion of this phase.
4. Prove the A2 extraction instance and close Q/conjugate-Q. The repository's
   `Sl3HighestWeightExistence` proves existence of a highest vector, not the
   needed full character/multiplicity formula. This is the main foundation
   risk. The compact Hom integral API likewise does not supply torus reduction.
5. Apply rank-nullity through the existing actual coefficient/kernel bridge,
   uniformly in the degrees. Deduce the support criterion from the structural
   multiplicity formula. A total classifier and regenerated CSV may follow,
   but are not required to establish the structural result.

Conjugation and exterior-complement duality may reduce work, after proving
equivariance. Complement duality carries a determinant twist: retain its
hypercharge and do not assume the neutral candidate domain is preserved.
Neither optimization is a prerequisite for the endpoint.

## Route B: rational constraints on zero-weight coordinates (fallback)

Under the revised endpoint, individual rank certificates from this route
are provisional milestones only. For final acceptance it must also yield a
uniform decomposition or symbolic rank/nullity proof for the matrix family.
Exhaustively certifying its finite instances is not a substitute for Route A's
structural conclusion.

Use an exterior basis to restrict candidates to simultaneous torus weight
zero, then build the raising/lowering constraints on that subspace. Prove
their common kernel equals the actual group invariants before using exact
rational rank certificates. Including both directions avoids relying on an
unproved assertion that highest vectors are invariant.

This replaces the A2 character theorem with explicit polynomial-action and
group-generation proofs. Existing finite group tests and rank certificates
are reusable, but their existence does not already prove this reduced matrix
equivalence. Measure zero-weight block sizes before choosing this route for
Q; sparse input alone does not guarantee manageable elimination/certificates.

## Acceptance and stop gates

Use L n=4,m=4,delta=4 and its conjugate as optional provisional tests, then
establish the uniform lepton theorem rather than filling rows one by one. Check
LLHH, exterior degree zero/top, dimension sums, and proven charge/parity
vanishing as regression controls. A failure of any control blocks promotion
of computed values. External integer computations may guide proofs, but the
individual values need kernel-checked evaluation/certificates. Completion
requires the structural theorem and its proved actual-group connection.

Proceed to Q only with a concrete A2 extraction proof plan or a measured,
feasible reduced-matrix construction. If either route needs a substantially
broader foundation, record its exact missing statement and reassess; do not
replace the endpoint with another conditional equality. No new dependencies,
arbitrary complex-number decision procedure, derivatives, EOM or IBP.

For later mixed contents, the additional structural target is
Source(c) equiv tensor_s exterior^(c_s)(V_s), equivariantly, giving dimension
product_s choose(dim V_s,c_s) and a multivariate character product. This is a
separate extension, not a gate for the 107 constant-content rows. A uniform
algorithm also does not imply that exhaustive mixed-content enumeration is
computationally feasible.

## Current counting continuation

Use the proved SL2 symmetric-power spanning property also to discharge compact
continuity: transport each generating orbit through TauCeti's continuous
symmetric-power model and extend by linear combinations. This does not add a
continuity premise to the actual polynomial sources. First prove the reusable
orbit/continuity adapter and the coefficient (rather than vector) A1 counting
adapter. Then combine two independent compact factors, construct the uniform
finite weight expansion, and connect its extracted integer to the L/Higgs
kernel. Retain the existing A2 gate for Q and the separate conjugate transport.


The current counting continuation is now implemented for L and conjugate L:
see [the uniform multiplicity result](lepton-multiplicity-results.md). The
proved local support predicate keeps degrees symbolic; no row-by-row rank
certificate replaces it. The remaining Q/color extraction is the exact A2
foundation at the recorded stop gate. The partial CSV remains unchanged.

## Authorized A2 continuation and Route B fallback

The user has authorized continuing stages 4--5 through either route, including
switching to Route B. The previous A2 stop gate is therefore reopened on the
existing topic branch. Route A inspection found GL Weyl-module irreducibility
and Schur-Weyl character identities, but no ready actual SU3 extraction or Q
exterior branching adapter. Pursue the Route B exact-coordinate connection:
replace transcendental circle samples by an explicitly infinite-order circle
point with rational real/imaginary parts, retain actual group exhaustivity,
then transport constant-Q exterior/Higgs basis coordinates and zero-weight
conditions. A matrix-family theorem must supply a uniform symbolic nullity /
support formula; a new abstract kernel/rank restatement or fixed-degree table
is not completion. No computations materializing enormous degree blocks are
authorized or required; the finite algebraic formula must stay symbolic.
The endpoint remains an unconditional actual Q/conjugate-Q connection and
rank-nullity/support theorem, with verified degree-uniform statements.


## Completed Route B variant

[Q/conjugate-Q result](q-gaussian-results.md) supplies the unconditional
actual-source connection and the uniform symbolic nullity/support formula.
The rational-coordinate construction uses the full exterior/monomial basis.
Zero-weight compression is a future efficiency optimization; the complete
constraint family and its Gram characteristic polynomial already prove the
same mathematical endpoint without that compression. The formula does not
consume an actual complex matrix or unevaluated kernel dimension as input:
its entries are generated by finite minors and explicit monomial sums over
Gaussian rationals. The degree-independent proof is not a table dispatch.
The A2 Haar/constant-term theorem of Route A is not claimed. Stage 5 is proved
for Q/conjugate-Q through the actual kernel bridge and rank-nullity. Together
with the L result this covers the neutral constant-content prerequisite;
mixed-content and residual classification remain outside this endpoint.


## External-library follow-up

The user requested assessment of ATLAS, LeanPool and other available libraries.
The [pinned source assessment](external-library-assessment.md) found an existing
mathlib product-exterior algebra equivalence suitable for the mixed-content
foundation, and LeanPool divided-difference relations as optional A2 helpers.
The inspected ATLAS v1 Weyl-character/constant-term statements use `sorry`
and cannot close the extraction premise. No dependency was added or pin changed.
Mixed-source multidegree/equivariance and the actual SU3 extraction theorem
remain the precise next proof obligations.


The subsequent [mathlib mixed-source continuation](mixed-mathlib-results.md)
proves the binary actual-source/spectator equivalences, character product and
SM dimension/rank connections for all distinct signed-species pairs. Arbitrary
multispecies iteration was subsequently proved in the result linked below;
invariant extraction remains open.


The [mixed-chirality comparison](mixed-chirality-results.md) now proves the
actual paired-to-independent compact Weyl coefficient equivalence for arbitrary
contents. Multispecies product decomposition was subsequently proved below;
A2 invariant extraction remains open.


The [finite-tree iteration](iterated-mixed-results.md) now constructs the
arbitrary finite-family statistical-source decomposition and its product
dimension/character/coefficient interfaces. Its proved label bijection and
field transport now connect every ordered content to the existing ten signed
species, with symbolic source dimensions, character products and actual local
matrix column counts. Invariant extraction/counting remains open; the product
formula does not itself evaluate neutral kernel dimensions.

## Authorized literature-input boundary

The user now permits established unformalized mathematics as explicit theorem
parameters, following the E6 convention. The [conditional Weyl plan](weyl-input-plan.md)
and [result](weyl-input-results.md) isolate Haar-to-torus constant-term reduction
from finite extraction algebra and actual-kernel consumers. This supersedes
the earlier requirement to prove all A2 foundations inside Lean for this
conditional route; it does not claim that the external premise is formalized.
The compact SM comparison, continuity and finite torus presentation remain
separate application obligations at that checkpoint; they are constructed in
the subsequent result below.


The subsequent [actual compact extraction result](compact-extraction-results.md)
constructs the combined compact coefficient comparison, joint continuity and
finite inverse-torus-character presentation. The final local dimension/rank/
support theorems need only the explicit Weyl reduction input. This closes
task III's application bridge under the authorized literature boundary.
The presentation uses classical torus spectra and is noncomputable; explicit
weight recurrences and numerical evaluation remain open, as does nontrivial
residual classification. No CSV entries are newly evaluated.


The [existing q/l consumer](ql-extraction-results.md) now composes the scalar
residual separation with the conditional local multiplicity positivity theorem.
Its all-degree iff eliminates every retained `Allowed(T)` within the existing
q/l action class. Numerical evaluation/572 recount and other residual classes
remain separate; no new residual separation premise is needed.
