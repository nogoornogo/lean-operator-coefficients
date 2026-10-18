# Frozen Target And Implementation Plan

## Mathematical Target

Supply finite fermion/boson alphabets, complex local and multiplicity carriers,
commuting local-group G and residual-group H actions, positive integral doubled
engineering weights and additive integer charges. Every species carries a local
G representation tensored with an arbitrary H multiplicity representation.
The physical consumer uses the existing SM gauge/Weyl fields and charge conventions.

For arbitrary natural n,m, begin with invariant **functionals** on
`Λⁿ Vferm ⊗ Symᵐ Vbos`, not a selected list of contractions. Derive the species
multidegree decomposition and impose engineering weight and specified charges
on its supported components. Charges restrict support; they do not assume a
new continuous charge symmetry or solve gauge neutrality by arithmetic alone.

For a field-content vector c, let L_c and M_c be ordered tensors of its local
and multiplicity carriers, and let S_c permute identical fermion and boson slots.
Construct the signed exchange quotient, with the fermion sign character and
trivial boson character. Define local G coinvariants intrinsically by

`(L_c)_G = L_c / span {g • x - x}`.

The proposed residual carrier is the signed exchange quotient

`Q_c = ((L_c)_G ⊗ M_c) / R_exchange`.

Prove, rather than assume, the local/residual tensor separation, descended
exchange action, and the equivalence

`C_c ≃ₗ[ℂ] Hom_H(Q_c, ℂ)`.

Coinvariants are appropriate because the project classifies maps **to** the
trivial representation. Do not replace them with invariant vectors, or replace
`Hom(W,ℂ)` with `Hom(ℂ,W)`, without proving additional hypotheses. Gauge
coinvariants and the exchange quotient must commute via explicit inverse maps.
No compactness or semisimplicity is needed as a premise for the proposed
universal-property route; this is a proof target, not an established theorem.

Local finite-dimensionality may be used only in a separately identified
finite-local consumer, not as a new restriction on arbitrary flavor modules.
Do not require a chosen local basis or a coefficient spanning certificate in
the principal theorem. Genuine group actions and the stated commuting action
laws are structural inputs and must be verified for the SM specializations.

## Milestones

### A. Gauge-Coinvariant Hom Descent

Inspect existing quotient and tensor universal properties. Prove equivariant
Hom descent, residual stability, and coinvariants of a local tensor arbitrary
multiplicity carrier. Prove compatibility with local exchange maps. Persist
the exact types and a strict transitive audit before moving to mixed assembly.

Two bounded routes are allowed in the initial feasibility pass:

1. Direct relation quotients and tensor universal properties (preferred).
2. Reuse the existing stable-relation Hom descent and commuting exchange
   quotient equivalences, with explicit natural comparison maps.

Failure requiring an essential new general foundation is reported with the
missing statement; it does not authorize an indefinite third route or a new
external mathematics premise.

### B. Arbitrary Mixed Statistics And Species

Extend the currently one-boson assembly to arbitrary boson slots using symmetric
power universal properties. Prove restriction/assembly inverses and all identical
species exchanges on actual carriers. Regroup local and multiplicity tensors,
then connect the quotient from A. Include zero-degree cases. Bose/Fermi exchange
is exact algebra throughout, not probabilistic processing or external computation.

### C. Grading And Uniform Criteria

Construct the weight/charge-supported coefficient spaces and prove their
residual-Hom product equivalences. Positive species weights imply finitely many
contents under each finite engineering bound, without fixing a numeric bound
such as seven or eleven in the mathematical theorem.

Prove total zero iff each residual factor is zero, and existential nonzero iff
some factor admits a nonzero functional. All-degree vanishing is equivalent to
vanishing at every finite degree. Do not claim an algorithm deciding arbitrary-H
Hom or a finite search cutoff for the unbounded problem.

Keep three objects distinct: the direct sum of finite-degree field carriers,
the product of their algebraic coefficient spaces, and finitely supported
coefficient families. The dual of an infinite direct sum is generally a product;
specify which interface is used and prove its component maps.

### D. Existing Consumers And Acceptance

Instantiate with the signed SM fermions and Higgs gauge-dual alphabet. Construct
comparison equivalences and commuting extraction/reconstruction diagrams with
the existing six/seven-dimensional BNV classifications, not merely matching
dimension counts. Preserve independent opposite multiplicities and explicit
scalar residual actions. Reuse their prohibition and nonzero controls.

Add small two-boson and mixed-fermion/boson examples to test the genuinely new
assembly, including exchange signs, inverse laws and vanishing from relations.
All tests are Lean theorems, not numerical or sampled checks. Update Math/Physics
aggregates and strict audits, run focused builds and `lake build`, layout and
documentation checks, then record verified assumptions and the final dossier.

## Stop Condition And Non-Goals

Stop after A–D and their verification. Checkpoints are not automatic permission
to merge into master. A counterexample to a proposed map or an essential large
foundation requires an explicit plan review.

Excluded: individual dimension-eight-to-eleven basis enumeration, AutoEFT
installation/output generation, a full Li p/y/m/j construction, derivatives,
field strengths, EOM/IBP, amplitudes, UV matching, rates and numerical dynamics.
Also excluded are unconditional inevitable BNV for arbitrary symmetries, a
uniform upper degree bound, or a claim that the existence iff computes Hom.
Exact baryon-number symmetry already prevents unconditional inevitable BNV.

No new dependencies, custom axioms, `sorry` or audit exceptions. The existing
seven-dimensional result remains checked even if the general route needs review.
