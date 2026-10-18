# SU(5) Transfer, Mass Conditions And Bounded Mixing Assessment

This records the first checkpoint `checkpoint 01`. The subsequently authorized
[mixed-mass phase](mixed-mass-result.md) closes the specified C2 actual-field
bridge for common scalar ten characters and arbitrary independent mass rows.
Its new statements do not enlarge the scope of the earlier theorems below.
The further [matrix-mass phase](matrix-mass-result.md) extends the common-scalar
Dirac class to arbitrary copy counts and species matrices, with automatic light
coefficient existence when source copies outnumber target copies.

The [normal-form/common-copy phase](normal-form-copy-result.md) subsequently
derives the Dirac ansatz from arbitrary invariant symmetric mass in the
scalar-copy class and proves a physical light coefficient for common non-scalar
copies with arbitrary equivariant species maps. Their simultaneous unification
and general completeness bridges remain [explicit](remaining-general-connections.md).

## Formal Result

The new [SU(5) source](../../../GUT/SU5/SelectionRules/ScalarBlockQque.lean)
uses the actual algebraic `10 = exteriorPower 2 Five` and `bar5`, with the
existing standard SM-cover branching. The carrier is algebraically equivalent
to the existing unitary models; `uvInner` transports their two Hermitian forms.
The result does not reuse the SU(6) carrier or its benchmark mass.

`Input H` supplies finite Abelian H, a genuine unitary representation U,
pointwise SU(5) lifts `diag(c I3,w I2)` and scalars a/b on the ten/bar-five.
Neither the lifts nor individual scalar factors are homomorphisms.
`diagonal_commutes` and `physical_commutes_sm` derive compatibility with SM;
`joint` constructs the genuine SM x H representation. UV commutation is not
assumed. A neutral diagonal adjoint could be fixed by this matrix action, but
no scalar-sector, vacuum or complete breaking certificate is constructed here.

The injective embeddings of Q, u^c and e^c into the actual ten have phases
`a c w`, `a c^2`, `a w^2`. Genuine species characters are derived from U.
Their physical qque character is trivial pointwise. The range coordinate maps
are invertible; gauge, residual and joint-action lemmas identify their
transported representations with the actual restricted actions.
`exists_actual_exterior` transports the existing named Lorentz/fermionic
coefficient to Q and the right-handed duals of u^c/e^c, preserving nonvanishing.
The standard coefficient's witness is 2. H acts trivially on spinors.
Unused d/L charge entries are placeholders; no duql theorem is asserted.

`trivialInput` inhabits the class for every finite Abelian H. `zeroMass_light`
proves all UV vectors are actual zero modes of the initial SM-invariant zero
mass. This is a pre-electroweak chiral control, not a generated mass model.

## Mass Formula Removed, Light Conditions Retained

`LightMass S` accepts an arbitrary symmetric bilinear H-invariant mass B,
SM invariance and certificates placing the three selected embeddings in its
radical. `LightMass.jointMass` derives joint SM/H mass invariance and proves
that its radical is the same submodule. `radical_stable` derives H stability.
`exists_light_exterior` combines actual light membership with the nonzero
physical coefficient, without using any specific mass formula.

These certificates remain hypotheses. Arbitrary invariant mass does not by
itself prove them, and the theorem is on the typed participating species,
not an untyped exterior power of the whole all-left radical. Different
masses/placements need their own field maps and action dictionary.

| Condition | Role | Current evidence |
| --- | --- | --- |
| Same-ten scalar/block action | Derives pointwise neutrality | New SU(5) Lean adapter |
| Genuine action | Derives species characters and joint action | New Lean lemmas |
| Mass invariance | Derives radical stability | New `LightMass` adapter |
| Three embeddings are zero modes | Makes the participating fields physically light | Supplied for arbitrary B; derived for zero mass and the orthogonal extension |
| Exact full light spectrum | Stronger model statement | Zero-mass control; extension retains the chiral subspace with total dimension 15; not inferred from an index |
| Shared UV copy after mixing | Sufficient construction choice, not a necessary coefficient condition | Finite mixed counter-control below |

## One-Copy Chiral Mass Assessment

Existing actual branching gives integral hypercharges `6Y`:
Q:1, u^c:-4, e^c:6, d^c:2, L:-3. No pair in this list sums to zero.
An SM-invariant complex-bilinear mass can pair only opposite hypercharges:
its two-field phase is `z^(q_i+q_j)`, so invariance for all z in U(1) forces
zero when the sum is nonzero. Thus the one-copy chiral carrier, and direct
chiral copies with this branching, have no such bare pre-electroweak mass.
This does not apply after electroweak breaking or to a larger carrier.

The table/pair exhaustion is checked exactly by
[the finite audit](../../../tools/su5-matter-mass-protection/audit_mass_patterns.py).
The preceding reasoning is a symbolic applicability assessment, not a new
Lean theorem classifying every invariant bilinear form. The physical branching
and conditional mass adapter are formal; table exhaustion is not a premise
of their proofs. There is no claim of a new nonzero mass on the chiral carrier.

## C2 — One Added Ten/Dual-Ten Pair

[ScalarBlockMassExtension](../../../GUT/SU5/SelectionRules/ScalarBlockMassExtension.lean)
adds one actual ten and its dual. The extra pair has the standard SM action
and trivial H action. Its canonical evaluation mass is multiplied by c;
the chiral carrier has zero mass and no mixing with that pair.

Lean proves joint invariance by the mass construction, nonzero mass for
c != 0, retention of all original light fields, and radical dimension
`15 + (if c = 0 then 20 else 0)`. The physical qque coefficient survives on
those retained participating fields. The UV matter dimension is 35.
No full-UV covariance of the extended residual action, UV Yukawa origin or
protecting interacting model is supplied. This is an explicit broken-phase
mass/light control, not all allowed mass forms on this matter.

For mixing, freeze two ten copies and one dual ten, trivial H, unchanged
bar-five and the canonical SM evaluation pairings. In each ten species take
one mass row (alpha,beta) into its dual. The exact rational control uses
Q:(1,0), u^c:(0,1), e^c:(1,1). It has symmetric mass rank 20 and radical
dimension 15. The surviving copy lines are respectively (0,1), (-1,0),
and (-1,1); their common intersection is zero. Each line is checked directly
against the full 35-by-35 mass matrix. Hypercharge invariance is checked;
full SM invariance is justified by the chosen per-species evaluation ansatz,
not computed by a scan of gauge matrices.

Consequently an exact SM light count does not force the three participating
species to come from the same UV copy. Trivial residual H still gives neutral
charges. The script is not a Lean instance or a proof of exterior transport
for this mixed carrier. The precise remaining bridge is an equivariant
species-by-species radical identification for these mass kernels and their
duals, rather than an assumption of a common UV-copy line.

## C1 — Multiple Copies And Residual Mixing

The existing Georgi-Glashow theorem already supplies physical exterior qque
for positive n, zero mass and a continuous compact UV-centralizer action,
including generation mixing. That verified theorem is reused by reference.
It does not cover an arbitrary scalar/block-twisted action without a new
actual-species transport or invariant tensor bridge.

A bounded exact two-copy C2 residual control sets a=-1, c=1, w=-1 and
uses copy swap A. The SU(5) matrix has determinant one; species matrices are
Q=A, u^c=-A, e^c=-A, each squaring to identity. Both copy eigencharacters
satisfy qque neutrality. On flavor tensor squares the nonzero map I+swap
intertwines Q tensor Q with u^c tensor e^c. This checks flavor neutrality and
an internal nonzero map, not a physical Lorentz/exterior model certificate.

The missing general C1 interface must take the actual compensated copy
matrices and derive the species representations and nonzero alternating
coefficient, or derive occupied simultaneous eigen-submodules and their
radical embeddings. The one-dimensional `NeutralQqueExterior` character
adapter cannot be applied to an entire mixing space merely by naming a scalar.

## Stop Decision

The SU(5) transfer and conditional mass adapter are proved; the nonzero
orthogonal mass control is proved. The two bounded matter routes have explicit
finite controls and identified actual-field obligations. This completes the
bounded proof/feasibility endpoint, not a general matter/mass classification.

Further implementation of source-derived mixed-kernel species adapters and
general compensated flavor actions requires freezing new theorem signatures
and their allowed mass/action families. These are the recorded next scope
decision, not an automatic additional search or evidence of protection.
SU(N), Spin(10), E6, arbitrary representations, matching and rates are deferred.

The subsequent [unified result](unification-result.md) derives species-equivariant
mass maps from arbitrary invariant symmetric B on the non-scalar carrier,
closing the formerly separate assumption-removal bridge.

The [target-unitarity continuation](target-unitarity-result.md) removes supplied
target unitarity from the unified endpoint, retaining compactness/continuity
and proving the conclusion on original participating ranges and original B.

The subsequent [algebraic common-copy result](algebraic-copy-result.md) proves
the arbitrary-B endpoint for arbitrary H with semisimple source only, removing
H topology/compactness/continuity and requiring neither target semisimplicity
nor invariant source/target metrics.

The [pure-carrier relaxation](algebraic-carrier-result.md) removes norm/inner-product
interfaces from the named arbitrary-B source-semisimple theorem, completing the
requested finite-dimensional complex common-copy statement on the current carrier.
