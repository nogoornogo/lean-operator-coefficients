# Arbitrary Copy Matrices: Derived Light Fields And Physical Qque

## Formal Statement

[MatrixTenMass](../../../GUT/SU5/SelectionRules/MatrixTenMass.lean) generalizes
the previous two-source/one-target row family to arbitrary finite p source
tens, q target tens, and one untouched bar-five. Actual all-left matter is
`((Fin p → Ten) × BarFive) × (Fin q → Ten)*`; the target dual is equivalent
to q dual-ten copies. Ten is the actual SU(5) second exterior power, with the
proved standard SM branching. Source and target tens share the same genuine
Circle character chi; the dual target has its dual action. Bar-five uses psi.
H is Abelian and acts trivially on spinors; no finiteness or topology is needed.

Three arbitrary complex q-by-p matrices independently mix up-left, Q and
electron-left. Their entries define actual weighted ten maps through the
branching equivalence, not an assumed charge table. `massMap` proves joint
SM-cover x H equivariance. `mass = ofDirac massMap` is a symmetric invariant
complex-bilinear form. There is no full-SU(5) invariant mass, UV scalar coupling
or vacuum certificate assertion, and no classification of all invariant forms.

`mem_radical_iff` proves, for every parameter value:

```text
(source, dual) is light iff M(source)=0 and dual annihilates range(M).
```

For each species matrix N, `kernel_dimension` proves
`p ≤ q + finrank(ker N)`. Consequently `q < p` implies a nonzero kernel vector
for each species, with no full-rank hypothesis. This includes zero targets,
zero matrices and partial ranks. Kernel choices are noncomputable algebraic
choices; no continuous parameter-dependent kernel basis is asserted.

`Kernels` records three nonzero vectors satisfying their respective matrix
kernel equations. These equations, rather than supplied light-membership
certificates, derive injective species maps into actual matter and its mass
radical. Q/up-left/electron-left may use different copy vectors. Action lemmas
prove that these maps intertwine the actual joint action, and range actions
match restrictions of `fieldsRho`.

`exists_light_exterior` constructs a nonzero physical SM/H/SL(2,C)-invariant
fermionic qque exterior coefficient on these actual participating ranges,
using right-handed duals for up/electron in the physical convention. It applies
to arbitrary p/q whenever `Kernels` is supplied. `rectangular_light_exterior`
derives `Kernels` from `q < p` and therefore applies to every triple of complex
matrices of that size, without any light-placement premise. Common chi ensures
physical neutrality; the existing neutral exterior construction is reused.

## Interpretation And Remaining Fixed Conditions

Within this mass family and common-character class, a positive source-minus-
target copy count prevents tuning the matrices to remove the constructed
physical coefficient. This is an all-parameter result, not a numerical scan.
The old shared UV-copy line and two-copy restriction have been removed.

For p ≤ q the automatic kernel argument does not apply: the conditional
`Kernels` theorem remains available, but nonzero kernels must be established.
There is no universal coefficient claim for these sizes, nor an iff statement
classifying all light coefficients. No exact full light spectrum is inferred
from the rank bound. The untouched bar-five restriction remains explicit.

Common scalar chi, the actual standard branching, species evaluation/Dirac
mass ansatz and trivial residual spinor action remain hypotheses. Arbitrary
flavor residual matrices, further representations and other mass couplings
are outside this theorem. A coefficient on participating species does not
by itself supply a coefficient on the full light carrier; that extension needs
an equivariant projection and exterior pullback certificate. No generated
Wilson coefficient, rate, proton lifetime or all-BNV protection test follows.

## Proof And Verification

The proofs derive actual embeddings and physical exterior transport, rather
than using a virtual chiral index as a light-field certificate. No literature
premise, custom axiom or dependency-pin change is introduced.
[AuditMatrixTenMass](../../../GUT/SU5/Audit/AuditMatrixTenMass.lean) persistently
checks all 47 named definitions/theorems transitively against the three standard
axioms and rejects original SU(6) import origins. See [verification](verification.md)
for focused/full build and repository checks. The frozen
[matrix-mass plan](matrix-mass-plan.md) defines the completed endpoint.
