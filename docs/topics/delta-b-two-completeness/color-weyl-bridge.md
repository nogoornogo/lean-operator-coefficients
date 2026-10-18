# Color-times-Weyl bridge on the actual quark domain

## Statement and scope

The domain is six copies of `Quark = Color ⊗[ℂ] WeylSpinor.Space`.
For an arbitrary multilinear coefficient invariant under independent color
`SU(3)` and right-Weyl `SL(2,C)` actions, there is a unique array
`c : Fin 5 → Fin 5 → ℂ` such that on every decomposable input

`f (v₀ ⊗ s₀, …, v₅ ⊗ s₅) = Σₚ Σ_q cₚq Cₚ(v) W_q(s)`.

Tensor-product basis extensionality proves that these values determine the
coefficient on **all** inputs, including nondecomposable quarks. This is not
an assumption that a quark or an invariant coefficient factorizes.

This closes the combined-domain spanning bridge. It does **not** prove that
species statistics reduces the array to two free coefficients. No new
physical assumptions, literature premises, dependencies or resource limit
overrides are used.

## Proof structure

1. Fixing spins gives a color multilinear map via the linear maps
   `v ↦ v ⊗ s`. Color reconstruction gives five coordinate functions of spins.
2. Each color coordinate is a linear combination of fixed-color evaluations.
   Those are invariant multilinear spin maps, so Weyl spanning applies.
3. `SixWeylMultilinear` transports the existing classification using six
   applications of mathlib's `curryRight`. Its triangular probe inverse
   proves reconstruction and uniqueness as multilinear-map equalities.
4. Substitution gives the 25-term formula with an input-independent explicit
   probe array. Applying both triangular inverses proves its uniqueness.
5. The tensor product of the color and spin bases and multilinear basis
   extensionality prove `pure_ext` and `eq_of_coordinates`.

## Connection to the intrinsic sector

`orderedCoefficient_invariant` derives both independent invariances from
the physical gauge/Lorentz intertwiner, by restricting to the corresponding
group elements. It does not impose extra hypotheses on intrinsic coefficients.

`exteriorRestriction` uses the proved exterior restriction, so decomposition
applies to arbitrary intrinsic intertwiners, not just constructed contractions.
`exteriorRestriction_speciesAlternating` derives signs under within-species
permutations from the exterior alternating map. Up/down interchange is not
included. `species_coordinate_constraint` gives explicit linear constraints
on the 25 coordinates.

`exterior_eq_of_coordinates` proves injectivity on the intrinsic degree
`(2,4)` sector. Its degree hypotheses are the existing bidegree condition:
they are needed for reverse reconstruction, not forward restriction/spanning.

## Completed endpoint

The species-statistics equations have now been reduced to an explicit
two-dimensional kernel, and the two-probe inverse is proved on the intrinsic
sector. See [the final classification](two-coordinate-classification.md).
This additional proof is needed: neither the Fierz relation nor the coordinate
injection alone supplies it. No conditional `spanning` or `rank = 2` parameter
hides the obligation.

## Sources and verification

- [Multilinear Weyl adapter](../../../Physics/FieldTheory/Spinor/SixWeylMultilinear.lean)
- [Combined-domain proof](../../../Physics/StandardModel/Operators/SixQuarkInvariant.lean)
- [Persisted strict audit](../../../Physics/StandardModel/Operators/Audit/AuditSixQuarkInvariant.lean)

The focused build and audit command is
`lake build Physics.StandardModel.Operators.SixQuarkInvariant
Physics.StandardModel.Operators.Audit.AuditSixQuarkInvariant`.
It passes 18 strict transitive axiom checks, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. The new source and audit have no warnings;
existing dependency warnings are unchanged.

`lake build` also passed (5947 jobs). Layout checks passed for 894 modules;
documentation link checks and `git diff --check` passed. This verified
milestone is extended by the final two-coordinate result; current verification
and the recorded integration target are in the [topic record](README.md).
