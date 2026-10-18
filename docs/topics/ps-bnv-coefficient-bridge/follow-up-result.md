# Follow-Up Result: Normalized Conditional Light Coefficient

## Outcome And Stop

The reusable normalization and invertible-pullback interfaces are proved.
The exact mu=0 component mass kernel is normalized in a supplied canonical
Euclidean kinetic form, and its actual exterior light coefficient has the same
zero/nonzero criterion. Finite neutral-VEV contraction and diagonal Phi
identities are checked. Full PS model admission and full paper-prefactor
agreement remain unverified: the two inspected convention routes did not close
the mixed-charge-conjugation/VEV normalization gate. This is the follow-up
plan's bounded convention stop, not paper-wide validation or refutation.

See the [frozen dictionary](follow-up-dictionary.md),
[follow-up plan](follow-up-plan.md) and [original conventions](conventions.md).

## Reusable Statements

[Math.LightLineNormalization](../../../Math/LinearAlgebra/LightLineNormalization.lean)
normalizes z != 0 by r=(norm z)^(-1), with the real r embedded in C.
The unit vector remains in the kernel of any complex-linear mass map.
A linear functional's value is multiplied by r, preserving nonzero. No finite
size, group, compactness or spectral decomposition is needed. The norm is
supplied, not derived from a kinetic action.

An alternating coefficient pulled back by a linear equivalence is nonzero iff
the original coefficient is nonzero. The change must be invertible within the
same light space; an arbitrary injection can restrict a coefficient to zero.
This reusable statement concerns actual coefficients, not scalar prefactors.
The existing Math audit includes six new strict transitive checks.

## PS Normalization Consumer

[NormalizedLight](../../../GUT/PatiSalam/Matching/NormalizedLight.lean)
uses EuclideanSpace C (Fin 3), avoiding the supremum norm of the raw function
space. For the previous chart z=(1,0,-d/M), define r=1/norm(z). Then:

- norm(r*z)=1 and the supplied mu=0 mass annihilates r*z when M != 0;
- the barred xi projection is star(r)*star(-d/M), nonzero iff d != 0;
- only the anti-neutrino coordinate in the existing light-field injection is
  multiplied by star(r); the quark coordinates are unchanged;
- the normalized coefficient equals the previous actual alternating
  coefficient composed with this invertible coordinate change;
- under Lambda,m,M != 0, nonzero iff w,v,y,Y != 0 and C_L != 0 or C_R != 0.

A specialization to M=y*star(v) retains the same nonzero condition, with
nonzero y,v ensuring M != 0. A normalized nonzero exact control and zero-UV
control are proved. No finite-mu normalized mass eigenstate theorem is claimed.
The coefficient remains conditional on the supplied mass/component and kinetic
conventions, even though its kernel and normalization are now derived within
those conventions.

## Finite Component Admission

[ComponentAdmission](../../../GUT/PatiSalam/Matching/ComponentAdmission.lean)
proves expansion of sum(star(chi[a,i])*f[a,i]) and its restriction to
chi[3,0]=v. The same vertex coupling yields -y*star(v)*f[3,0]. It also expands
the holomorphic mass action -1/2 sum(x_i M_ij x_j), and checks the diagonal
restriction of tau2*conjugate(Phi)*tau2. The resulting two Dirac entries are
 y*h1+yt*star(h2) and y*h2+yt*star(h1).
Selecting h2=0 does not eliminate the conjugate direction: the second entry
is still yt*star(h1). The supplied hypercharge eigenvalue dictionary gives
6Y=(4,-2,0,-6) for u,d,nu,e and makes the neutral VEV uncharged.

These are finite component identities. They do not certify the PS group action,
full branching/stabilizer, the complete Phi Yukawa contraction on spinors, or
the translation of the paper's barred fermions into the supplied holomorphic
mass chart. The existing UV epsilon/exterior certificates are reused. Defining
an array or checking charge arithmetic does not establish those missing maps.

## Source Gate And Remaining Inputs

The source [2211.02054v2](https://arxiv.org/html/2211.02054v2), Eqs.(2),(10)–(14),
uses vR=sqrt(2)*componentVEV while the neutral vertex and displayed matrix
require a still-unverified normalization/charge-conjugation translation.
The predecessor [2012.05976v2](https://arxiv.org/pdf/2012.05976v2),
Eqs.(2.10),(2.15),(2.17), uses a different VEV convention and explicit mass
factor 1/2; it cannot supply that conversion unchanged.

Derived here: kernel normalization, coefficient coordinate transport, finite
neutral contraction and diagonal Phi algebra. Supplied: kinetic form, mass
chart's physical dictionary, selected vacuum, UV C_X and original sector
admission. Unresolved: complete source-to-chart translation and full normalized
Eq.(24) comparison. No numerical rate, hierarchy fit, hadronic amplitude or
full proton-stability conclusion follows.

[Verification](follow-up-verification.md) records the acceptance checks.

## Later Source-Action Translation

The [later action result](action-translation-result.md) explicitly tracks
source coupling conjugation and canonical kinetic terms, and records a
definite heavy-entry magnitude discrepancy in that convention. This earlier
normalization certificate retains its conditional meaning.

## Subsequent Representation Bridge

The later [representation admission](representation-admission-result.md)
constructs the SM-cover homomorphism and complete fL/fR/chi component maps,
with Phi columns in an explicit dual-index convention. It closes the
covering-group branching-map gap recorded at this checkpoint; full invariant
action matching and source-normalization comparison remain open.

## Subsequent Action Comparison

The [action comparison](action-comparison-result.md) closes internal Yukawa and
UV gauge-kernel checks and the selected factor-four correspondence. It also
proves that the displayed light ratio is not in the derived canonical mass
kernel, including after normalization. Full signed source-action equality
remains unverified; the comparison is not a paper-wide correctness judgment.
