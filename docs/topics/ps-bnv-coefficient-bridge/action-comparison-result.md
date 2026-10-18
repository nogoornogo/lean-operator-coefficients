# PS Action Comparison: Gauge Core And Canonical Light Restriction

The new representation maps close further action-comparison obligations:
the chi Hermitian contraction and direct Phi Yukawa gauge contraction are
PS-invariant, and the UV determinant kernel gives the previous selected factor
four. The complete signed fermion-action comparison is not closed. In the
fixed canonical source dictionary, the displayed light ratio still fails the
exact mu=0 mass-kernel test, including after normalization.
See the [plan](action-comparison-plan.md) and
[verification](action-comparison-verification.md).

## Pinned Comparison

Source: [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/html/2211.02054v2),
[PDF](https://arxiv.org/pdf/2211.02054v2),
[publication](https://doi.org/10.1103/PhysRevD.107.035019).
The operator, mass and coefficient formulas are checked separately; no rate,
finite-mu diagonalization or ultraviolet-origin claim is imported.

| Source target | Checked correspondence | Limit |
| --- | --- | --- |
| Eq.(10), chi-dagger fR | Full internal Hermitian contraction invariant under arbitrary PS element; exact same finite array contraction as before | Spinor singlet/barred conventions remain in the earlier chiral interface |
| Eq.(6), direct Phi term | Full Phi operator covariant; Hermitian fL/Phi/fR contraction invariant; arbitrary Phi matrix gives the complete finite index sum | The tau2-conjugate Phi identification for arbitrary PS action is not newly proved |
| Eq.(19), both X=L,R | Determinant/epsilon internal gauge kernel invariant for arbitrary PS element | Ordered internal kernel; not a full Grassmann operator-to-registered-sector equivalence |
| Eqs.(20),(21) | Selected scalar/fermion-order sum yields 4 epsilon3 and agrees on every color basis triple with UVComponent.component; 1/4 cancels algebraically | The four-order sum retains the prior supplied symmetric fermion-bilinear convention |
| Eqs.(12),(14), mu=0 | Displayed-ratio light vector is not in the translated canonical mass kernel for nonzero Dirac/heavy data; normalizing it does not repair this | Fixed complete canonical reading, not every possible paper convention |
| Eq.(24) | Earlier scalar elimination and actual coefficient remain valid with the derived mass chart | Substitution of the displayed mixing ratio into that chart is not certified |

## Full Internal Yukawa Contractions

[InvariantAction](../../../GUT/PatiSalam/Matching/InvariantAction.lean)
proves preservation of the Hermitian form by unitary matrices and then by the
actual PS tensor representations, using tensor-product induction rather than
only component weights. Thus the earlier ComponentAdmission.contraction is
invariant on the transported chi/fR arrays under every PS group element.

For Phi=Hom(TwoR,TwoL), the full operator idFour tensor Phi satisfies
Phi(g) fR(g) = fL(g) Phi. The full Hermitian contraction with fL is invariant.
For arbitrary matrix m, its array evaluation is exactly the sum over all
color, left weak and right weak indices, with entries star(l[a,i])*m[i,j]*r[a,j].
This checks the direct Yukawa gauge contraction before choosing a vacuum.
Complex commuting coordinates represent the internal gauge kernel; they are
not silently substituted for a noncommutative fermion action. The earlier
selected chiral/Grassmann identities retain their own hypotheses.

## UV Internal Kernel And Selected Factors

[UVGaugeCore](../../../GUT/PatiSalam/Matching/UVGaugeCore.lean)
uses the determinant on four SU(4) vectors and two SU(2) epsilon pairings.
Its RR and LR invariance follows from determinant one for the corresponding
PS factors. The color/neutral restriction is exactly epsilon3. Swapping the
last scalar slots negates epsilon4; the two scalar and two supplied symmetric
fermion orders yield 4 epsilon3. Equality to the older finite oriented integer
component is proved for all color basis triples. Before resolving the two left
weak components, the scalar-order sum is -2 epsilon3 epsilon2.

With Lambda nonzero, C/(4 Lambda) times v times this selected sum is
(C v/Lambda) epsilon3. Taking v=vR/sqrt(2) reproduces that selected source
prefactor. This internal-kernel identity does not by itself prove the signed,
Lorentz-bearing UV polynomial descends to exactly the previously registered
SM/LEFT alternating coefficient.

## Exact Canonical Light Comparison

[DisplayedKernelComparison](../../../GUT/PatiSalam/Matching/DisplayedKernelComparison.lean)
proves a reusable algebraic test: for d and K nonzero, the vector
(1,0,-d/K) is in the kernel of mass(d,M,0) if and only if M=K.
Apply it to the earlier source translation d=-star(yPhi) w and
M=star(yR) vR/sqrt(2). The source-display choice K=yR vR has a different
norm when yR,vR are nonzero, so that vector is not in the derived kernel.
Its normalized unit vector is also not in the kernel: multiplying by a
nonzero normalization scalar cannot change kernel membership.

This strengthens the earlier squared-entry check to an actual light-field
restriction mismatch within the same dictionary. It does not independently
prove that the dictionary exhausts source conventions. An alternative complete
field/kinetic/coupling convention would need its own simultaneous mass and
vertex derivation; changing one displayed entry in isolation is not that proof.
The earlier normalized nonzero criterion is still valid for its derived chart.

## Bounded Stop And What Is Still Missing

The two UV comparison routes (determinant covariance and finite component basis)
close the internal gauge and selected-factor checks. The remaining interface
is a complete PS Grassmann/Lorentz polynomial with equivariant barred/conjugate
fields, symmetric bilinear ordering and scalar symmetry, followed by a proof
that its full restriction equals the registered typed coefficient. Separately,
the tau2 conjugate Phi channel needs a full PS equivariance adapter if the
arbitrary second Yukawa coupling is retained. Existing selected Phi slices
and fermion brackets do not establish those full interfaces.

This invokes the frozen typed-transport stop rather than starting a new
statistics foundation. Neither a complete paper-validation theorem nor a
paper-wide error theorem follows. A UV coefficient remains an explicit input;
allowed-space nonzero is not automatic generation, and generated tensor
nonzero is not a decay-rate or all-channel stability theorem.

## Common-Scale Follow-Up

The [common-scale result](common-scale-result.md) proves that a nonzero
common matrix factor preserves the local mismatch, distinguishes this
completed gate from full signed coefficient certification, and compares
the relevant published formulas. Independent field rescalings and arbitrary
kinetic metrics remain outside the theorem.
