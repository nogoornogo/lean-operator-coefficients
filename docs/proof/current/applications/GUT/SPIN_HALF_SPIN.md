# Compact half-spin source

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Construction

The construction works for Spin(2n). Write a real vector as `(x,y)`, with
all real coordinates first, and map it into the complex split quadratic
space `(C^n)* x C^n` by

```text
(x,y) |-> (z |-> sum_j (x_j - i y_j) z_j, x + i y).
```

This is a real-linear injection, and evaluation of the split quadratic
form is exactly the real sum `sum_j (x_j^2 + y_j^2)`. Thus it respects the
positive-definite **real** form; it does not identify compact Spin(2n) with
a split real Spin group. The Clifford universal property extends this to
a real algebra homomorphism into the complex Clifford algebra. A graded
induction proves that even elements map to even elements.

Pinned TauCeti supplies the complex split polarization, the even Clifford
action on its even exterior module, and the dimension formula. Composing
the new map with that action and restricting to the actual real Spin group
constructs `HalfSpin.representation n`. The chosen isotropic space has
dimension n, so the even module has dimension `2^(n-1)` for n > 0, hence
16 at n = 5. No abstract highest-weight classification is used.

Every matrix coefficient is a real-linear functional of the real even
Clifford element. Finite-dimensional module topology and the actual Spin
subtype topology therefore give continuity. The project's group-independent
finite-basis Hilbertization and TauCeti's compact-group Haar unitarization
give `unitaryModel`, with a representation equivalence and equality of
characters. This changes the Hilbert coordinates, not the representation
or its character. No topology is replaced by a discrete or indiscrete one.

## 4. Proof structure

### Spinorial Control

The scalar central element `-1` projects to the identity in SO(10) but acts
as `-Id` on the constructed module. Its character is `-16`, also in the
unitary model, whereas the identity has character 16. The algebraic action
is proved not to factor through the actual Spin-to-SO projection. This
guards against substituting a vector/tensor representation pulled back
from SO(10). It is not a proof of SU(5) branching or irreducibility.

The persistent audit also checks the one-dimensional n = 1 case, continuity
at n = 0, and positive norm-square on an imaginary-coordinate axis. It
forbids transitive SU(5) matter, SU(6), and USp imports. See
[the implementation record](interfaces/spin-half-spin.md).

### Exact SU(5) Exterior Comparison

The full Fock action of the actual compact Spin group conjugates real
Clifford generators by its actual orthogonal projection. Along the checked
SU(5) inclusion, that projection is the realification of the defining
complex action. In the chosen polarization, the isotropic W coordinates
carry that defining action, while the other isotropic summand carries its
contragredient, with an inverse in the covector pullback. Exterior
functoriality intertwines both creation and contraction. Consequently the
actual lift and the exterior action implement the same generator action.

Equality does **not** follow from that observation alone. The comparison
is completed in the following checked steps:

1. The real compact generators complex-span the split polarized vector
   space. The commutant identity extends to all complex generators.
2. Pinned TauCeti's surjectivity of the full Clifford action onto the full
   Fock endomorphism algebra, followed by a rank-one-operator argument,
   proves that every such commuting operator is scalar. This is not an
   assumed irreducibility theorem for the compact half-spin restriction.
3. Composing the inverse exterior action with the actual action therefore
   gives a specifically constructed nonzero scalar multiple of the identity.
   Because exterior maps fix the algebra unit, this scalar is a matrix
   coefficient of the actual action; it is multiplicative and continuous.
4. A new group-independent theorem proves every continuous complex scalar
   character of a compact, simply connected, locally path-connected
   topological group trivial. Compactness forces modulus one. The circle
   character lifts through the exponential cover to the real additive group,
   where compactness forces it to vanish.
5. Applying that theorem with the already proved SU(5) topology removes the
   scalar. `actual_eq_exterior` holds on the full Fock space and
   `halfSpin_eq_exterior` on the constructed even half-spin space.

The Fock algebra unit is fixed by SU(5). Here "vacuum" in declaration names
means this algebra unit, **not** a chosen Higgs VEV or a dynamical vacuum.
No physical symmetry-breaking assumption is added.

Persistent controls include an incorrect forward covector transformation,
the scalar ambiguity between `Id` and `-Id`, the zero-rank commutant, and
nontrivial circle/real characters when simple connectedness/compactness
is unavailable. Generic audits forbid gauge-family imports; the Spin
comparison audit forbids SU(5) matter, SU(6), and USp imports.

### Oriented Character Branching

For each actual SU(5) element, the defining unitary representation has an
eigenbasis with circle-valued eigenvalues. A reusable theorem constructs
this basis by restricting a unitary action to the cyclic group generated
by the element, using the existing Abelian character decomposition. No
simultaneous eigenbasis for the non-Abelian group is asserted.

Transport that basis to the polarized W coordinates. Its exterior vectors
indexed by even subsets of five indices are 16 independent elements of
the actual half-spin space and hence a basis. The checked exterior-action
comparison gives their eigenvalues as products of the defining eigenvalues.
Taking the trace and grouping subsets by cardinality gives degrees 0, 2,
and 4. Degree 0 contributes 1; degree 2 is the existing actual `Matter.ten`.
The product of the five eigenvalues is the actual determinant, namely 1,
so the degree-4 products are the inverse defining eigenvalues, the trace
of `Matter.antifundamental`. This derives `1 + 10 + bar5`, not `1 + 10 + 5`.

`SU5Branching.halfSpin_character` proves this identity on all SU(5) elements;
`unitary_character` transfers it through the existing representation
equivalences. `unitary_dual_index` proves that the singlet cancels when
subtracting the dual character. These conclusions use actual traces,
not a supplied branching certificate or a dimension-only argument.

Persistent controls cover an empty eigenbasis, repeated eigenvalues,
failure of the degree-4 inverse formula without determinant one, and an
actual SU(5) diagonal element distinguishing `bar5` from `5`. The generic
audit forbids gauge-family imports. The branching audit deliberately
allows SU(5) matter, while still excluding SU(6) and USp dependencies.

### Actual Positive-Target Model

`HalfSpinBenchmark.rho` is the constructed compact half-spin unitary action
on the actual 16-dimensional Hilbert space, extended to Spin(10) x H by
ignoring H. This works for any Abelian H, including finite groups; for a
topological group H the action is jointly continuous in the original
compact Spin topology. No new representation or branching certificate is
assumed. This example has a **trivial**, not a faithful or nontrivially
charged, residual action.

The actual SU(5) matter trace formulas identify the restriction to the
physical torus with one neutral SM generation plus one neutral singlet.
The exact dual light target follows by symmetric-mass index conservation
for **any invariant symmetric mass on this restricted action**. The
specific `model` and `continuousModel` choose zero mass, so their radical
is the full 16-dimensional space. An actual radical/source equivalence
gives equality of full characters; faithful evaluation then identifies
the complete torus/residual spectrum, not merely the dual index.

Each oriented SM weight has dual-index coefficient 1 and a proved nonzero
radical eigenvector. The singlet has multiplicity 1 but dual-index
coefficient 0. The common selection-rule theorem therefore applies to
this inhabited model and excludes universal prohibition of the supported
signatures. Persistent audits instantiate Z/3 with its discrete topology
and Circle with its usual topology, check physical-torus compatibility,
and reject zero-generation and negative-orientation reinterpretations.

## 6. Scope and limitations

### Current Boundary

**SPIN-2a/b/c are LEAN-CHECKED.** The actual
compact real Spin(10) group has a constructed 16-dimensional complex
representation on the even exterior spinor module, with continuous matrix
coefficients and an equivalent jointly continuous unitary Hilbert model.
Neither a representation nor an invariant inner product is supplied as a
certificate. The source is the same compact Clifford carrier used by
[the checked SU(5) inclusion](SPIN_STANDARD_CHAIN.md).

The actual SU(5) lift acts exactly by the exterior action, with no scalar
twist. Its character is now proved to equal **`1 + 10 + bar5` on every
SU(5) element**, in the current positive orientation, both algebraically
and in the continuous unitary model. This is a character-level branching
theorem, not an explicit direct-sum representation equivalence or a proof
of compact-restriction irreducibility. An actual continuous standard-chain
model is now constructed with trivial residual action, zero invariant mass,
and a positive one-generation target derived from these traces.

### Scope Retained

SPIN-2's acceptance gate is closed. The universal standard-chain theorem
still retains the ordinary-Abelian action, invariant mass, and exact dual
light-target conditions for arbitrary matter; this benchmark derives the
target for its particular source. Its full-spectrum result uses zero mass
and does not extend to all invariant masses. The light singlet is retained,
so even this example is not an SM-only full-spectrum claim.

No exact SM vacuum, realistic masses, compact half-spin irreducibility,
explicit direct-sum intertwiner, or nonzero decay amplitude is claimed.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
