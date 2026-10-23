# Paired Weyl Generated Input

Import [PairedWeylGeneratedInput](../../../../../Physics/FieldTheory/Jets/Weyl/Equations/PairedWeylGeneratedInput.lean).
`Physics.PairedWeylInput.generated` is the optional generated input for the fixed
ordered density chi_0 E_0(psi) + chi_1 E_1(psi). The independently specified
Pauli equations use signature (+---) and the existing actual left and
entrywise conjugate SL(2,C) representations.

The [Math calculation](../../../../../Math/Algebra/Constructions/PairedWeylKinetic.lean)
computes all four odd Euler components and all four zero even components.
Odd reordering and IBP signs are explicit. Its component differential
closure agrees with the helper's complete generated equations and IBP.
The [physical source](../../../../../Physics/FieldTheory/Jets/Weyl/Equations/PairedWeylInput.lean)
embeds both existing Weyl seed maps into the full exterior/polynomial jet
algebra and proves their actual Lorentz covariance. Multiplicativity and
covariant derivatives preserve the complete two-sided equation closure
and full divergence range, including arbitrary spectator products.

The physical Pauli-row dictionary and its complete equation-parameter span
identify that direct input with the generated density's full relation module.
`coefficientEquiv` has both inverse laws; `evaluation_agrees` preserves all
source evaluations. `candidate_extraction` transports the earlier literal
C5 expression to the equation input. `current_ibp` supplies ordinary IBP
inside that actual input. These statements do not assert nonzero support
or Lorentz invariance of that particular literature candidate.

The even labels are off-shell Higgs component spectators with Lorentz-scalar
field action. Higgs EOM, weak/hypercharge action, interacting Yukawa terms,
analytic action/Hermiticity and a Minkowski four-component current dictionary
are not included. The separate Higgs generated input cannot be silently
combined with this input to infer those additional results. No complete
dimension-eight coefficient basis is certified.

See [usage and stops](../../../../topics/derivative-literature-foundations/mixed-input.md)
and the persistent namespace-wide strict foundation audits.
