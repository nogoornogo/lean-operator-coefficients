# Verified Scope and Result Map

The source is [BgwZ6Selection](../../../Physics/StandardModel/Operators/BgwZ6Selection.lean).
It constructs cyclic scalar representations on arbitrary complex multiplicity
modules for each of the ten signed SM fermions and the two Higgs scalar species.
No finite-dimensionality or fixed generation count is required algebraically.

## Paper Dictionary

`printed_dictionary` matches the paper's left-handed Q, uc, dc, l, ec and H
charges modulo six. `fermion_conjugates` and `higgs_conjugates` check opposite
labels. Physical uR/dR/eR have opposite charges to printed uc/dc/ec. The
existing hypercharge convention is 6Y and baryon convention is 3B.
`fermion_identity`, `boson_identity`, `total_identity` prove the integral identity

```
3 * discreteCharge = 6Y - 3B + 9L.
```

This clears the fractions in the paper's relation, rather than treating 3B
as B. The right-handed-neutrino species is excluded from the alphabet.

## Actual Actions and All-Degree Prohibition

`copies`, `flavor`, `scalarFlavor` construct the residual Z6 representations.
`field_scalar` and `scalar_scalar` derive their scalar action on actual
SM gauge/Weyl tensor fields, including the charged Higgs copy factor.

`charge_of_nonzero` uses actual invariant functionals, scalar action on pure
mixed tensors and faithful cyclic character neutrality. `baryon_divisible`
combines it with the already proved local hypercharge neutrality to derive
that total 3B is divisible by nine for any nonzero pure-species coefficient.
This is a necessary condition, not existence for any multiple of nine.

`forbidden_values` eliminates absolute Delta B=1 and 2. `all_forbidden` uses
the existing composable B1/B2 specification on actual inputs and pure-species
extensionality to prove total prohibition at every mixed degree.
`residual_forbidden` transports that result through the existing decomposition
into its residual-Hom product. The field dictionary is not assumed complete
from charge counts alone.

## Charged-Higgs LLHH Existence

The follow-up source is
[BgwChargedHiggsWeinberg](../../../Physics/StandardModel/Operators/BgwChargedHiggsWeinberg.lean).
It uses actual lepton species 3 and Higgs species 0 with one complex copy each.
Their Z6 weights are two and one. `lepton_scalar` and `higgs_scalar` derive
these twists relative to neutral-copy actions; `phases` proves that two copies
of each cancel. `neutralEquiv` transports the whole exterior-degree-two tensor
symmetric-degree-two domain, without identifying a charged Higgs alone with
a neutral one. `leptonEquiv` and `higgsEquiv` then identify the neutral-copy
fields with the existing physical Weinberg input, removing the trivial Higgs
copy through the tensor right-unit equivalence.

`domainEquiv` composes these proved action identifications.
`coefficientEquiv` identifies the actual charged-field LLHH coefficient space
with complex numbers through `WeinbergSMInterface.oneGenerationEquiv`.
`witness` is the inverse image of one; `witness_coordinate`, `witness_nonzero`
and `exists_nonzero` certify its coordinate and nonzero existence.

The initial checkpoint had only `llhh_neutral` and recorded the mismatch with
the trivial-residual-Higgs adapter. The authorized follow-up resolves that
mismatch on the whole LLHH domain. It does not assert a single-field charged
to neutral equivariance. This is one-generation coefficient existence, not
arbitrary-copy mass classification or a coefficient generated in the UV.

## Exclusions

The algebraic action exists on arbitrary copies, but this does not certify
anomaly cancellation, three-generation consistency of the quantum theory,
UV gauge origin, spontaneous breaking or a full model including right-handed
neutrinos. Derivatives, EOM/IBP, dimension-15 minimality and rates are excluded.
The paper's all-operator claim is compared only within our derivative-free
SM/Higgs coefficient domain. Supersymmetric candidates are excluded.
