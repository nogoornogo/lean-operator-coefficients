# Verified Result

The source is [KorenSMSelection](../../../Physics/StandardModel/Operators/KorenSMSelection.lean).
The signed dictionary follows Table I of
[2204.01741v2](https://arxiv.org/pdf/2204.01741v2): the paper's B is quark
number b=3B_usual; l=L. Printed Q, anti-u, anti-d, L, anti-e are repository
species 0,6,7,3,9. Opposite charges are proved; Higgs and its opposite are neutral.

For H=Z9 times Z3 the action on content (b,l) has character
chi((a,c),(b,l)) = stdAddChar_9((b-3l)a) stdAddChar_3(lc).
`embedding` and `embedding_injective` identify H with a subgroup of Circle
times Z3; `chi_restriction` proves this is the restriction of continuous weight
b-3l and discrete weight l, rather than merely an unrelated charge table.

`neutral_iff` proves that all H elements act trivially exactly when
9 divides b-3l and 3 divides l. Consequently 9 divides b. `detect` excludes
the union abs(b)=3 or abs(b)=6 or abs(l)=2. `target_union` identifies this
with the nested union of three stable specifications. Absolute signs include
both an operator and its conjugate.

`copies`, `flavor` and `scalarFlavor` construct actual representations on
arbitrary complex copy modules. No finite-dimensionality is required.
`all_forbidden` invokes the existing ComposableBLSupport character consumer,
which retains the actual gauge/Weyl actions and exterior/symmetric statistics.
It proves zero for every coefficient in the selected support at every fermion
and scalar degree. `residual_forbidden` transports this result through the
existing coefficient decomposition to its product of residual Hom factors.
The representation and detection premises are discharged, not left as model
hypotheses.

`llhh_detect` is a charge-level check at (b,l)=(0,2). The all-degree result
already excludes actual selected LLHH coefficients. There is no nonzero
witness claim for any neutral content. The finite subgroup does not enforce
exact b-3l=0 and is not equivalent to the full continuous symmetry. Its weaker
selection is sufficient for the three requested prohibitions.

The paper's three-color, three-generation symmetry is the physical motivation.
The algebraic result does not establish anomaly freedom for arbitrary modules,
quantum survival, a complete EFT/UV model, proton decay rates, or neutrino masses.
Adding arbitrary symmetry-breaking operators invalidates its application.
LFV is not excluded by these total B/L charges. Derivatives and EOM/IBP remain
outside the coefficient input. See [verification](verification.md).
