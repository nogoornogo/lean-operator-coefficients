# Actual Selected-Species Extraction: 50 Checkpoint

The [continuation plan](sm-extraction-plan.md) closes the 50 and dual-50
selected-species/pairing gate. The 40 extraction and combined arbitrary-mass
presentation remain open; the overall physical endpoint is not complete.

## Proved for actual representations

[ExoticHyperchargeBasis](../../../GUT/SU5/Branching/ExoticHyperchargeBasis.lean)
uses the actual `tenEquiv` to transport an explicit SM-block basis to Ten.
The true U(1) action has basis eigenweights -4,1,6. TauCeti's actual symmetric
quotient basis theorem then derives all eigenvalues on Sym² Ten.

At the exact phase ZMod.toCircle(1:ZMod31), every such eigenvalue differs from
weights -6,-4,-1,1,4,6. The proof uses faithful characters and finite integer
identities inside Lean, not a computed profile or assumed scalar decomposition.
Basis coordinates prove absence of these eigenvectors in the full symmetric
square, and hence in the actual 50 kernel.

The dual-kernel result is also derived, not assumed: subtract the opposite
scalar eigenvalue from the finite-dimensional kernel action. Absence of a
kernel eigenvector makes this shift injective, hence onto. A putative dual
eigenfunctional then vanishes on its full range.

For any source representation with one of these scalar hypercharges:

- `fifty_hom_zero` and `fifty_dual_hom_zero` prove every map into actual 50
  or dual 50 vanishes;
- `fifty_hom_finrank_zero` and `fifty_dual_hom_finrank_zero` prove the exact
  full Hom dimensions are zero;
- `fifty_no_pairings` and `fifty_dual_no_pairings` exclude invariant bilinear
  mass pairings with 50 or dual 50;
- `selected_no_pairings` instantiates Q, uc and ec using the existing actual
  SM definitions and proved hypercharges. Opposite charges are covered too.

Thus arbitrary 50/conjugate copies cannot add mass partners for these three
species under the specified SM action. Existing finite-copy pairing lemmas
can extend the zero result to any copy count. No continuity, residual charge
choice, matrix entry, scalar or VEV is a premise of this SM-level exclusion.
The theorem is not an anomaly/phenomenological viability check, and does not
forbid the separate down-sector components of 50.

## Difference from previous profile checks

Previously these zeros appeared only in formal character lists. Here the maps
have the actual constructed invariant kernels as their targets. No supplied
branching equivalence, copy-count certificate or generic no-pairing hypothesis
is used to establish the zero conclusion. A full decomposition of all 50
spectators is unnecessary for this selected-species result.

## What remains for 40

40 has selected hypercharges in common with nonselected color/weak sectors.
A single U(1) phase does not separate those sectors. Its exact Q/uc copies,
the absence of an electron singlet, and the absence of additional opposite
partners therefore need an actual color/weak extraction argument.

The current assets include fundamental/ten branching and epsilon-contraction
uniqueness, but not the completed decomposition of the restricted kernel.
The explicit route must connect these contractions to that kernel and prove
injectivity, exhaustiveness and complementary-sector pairing exclusion.
The faithful-character route would need a proved actual multiplicity evaluator
for the higher tensor blocks. These are the next theorem-level prerequisites,
not consequences of the new 50 result or of dimension 40.

The next bounded milestone should treat the 40 charge-six sector as a kernel
of the color contraction and distinguish it from the electron singlet, then
extract Q/uc with the required color/weak contractions. Until this is done,
`SpeciesSectorPresentation` for the combined 10/bar5/40/50 carrier is not
supplied, and no all-mass physical qque conclusion is claimed.

## Checkpoint status

Completed: actual 50/dual-50 selected Hom multiplicities and mass-pairing
exclusions. Open: 40 selected-species extraction and combined all-mass adapter.
The construction plan's new-branching-prerequisite gate remains explicit;
no general representation/Young classification or physical model completion
is silently started or declared. See [verification](verification.md).
