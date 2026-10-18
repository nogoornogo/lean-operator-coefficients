# Flavor Restriction and Charged-Scalar Domain Controls

## Scope and Sources

The [result record](../../../../topics/flavor-quarticity-controls/results.md)
certifies bounded algebraic interpretations of two non-supersymmetric papers:
[DGT 2202.05275v2](https://arxiv.org/abs/2202.05275v2), Secs. II–III,
Tables I–II, and [quarticity 1606.04543v1](https://arxiv.org/abs/1606.04543v1),
Table I, Sec. II. Source charge assignments motivate explicit representations;
no anomaly, quantum-survival, vacuum, mass, matching or rate theorem is assumed
as a custom axiom or established by these certificates.

## DGT Restriction

[Source](../../../../../Physics/StandardModel/Operators/DgtFlavorRestriction.lean)
fixes m=1,n=3 and three gauge-basis flavor coordinates. It proves an injective
Z9-to-Circle homomorphism and the actual signed SM/Higgs action restriction.
Residual B1/B2 prohibition follows through the existing composable input and
its residual-factor equivalence. Dipoles use their separate actual B/W
coefficient equivalence: selected muon-to-electron/tau coordinates vanish
under Circle, and each has a residual invariant coefficient evaluating to
(1,0). The residual flavor Hom restriction is not surjective. The electron
right flavor action is proved equal to the lepton flavor action used by the
dipole adapter. No complete leptoquark/right-neutrino field admission, dipole
UV generation, physical flavor rotation or common-domain merger is claimed.

## Quarticity Adapters

[Source](../../../../../Physics/StandardModel/Operators/QuarticityAdapters.lean)
constructs a right-Weyl neutrino, neutral under the full SM gauge cover, with
Z4 times Z2 charges (1,1), and an eta singlet of charges (2,0). Eta's phases
are proved real signs; the coefficient carrier is complexified. A bare
exterior-square invariant coefficient must vanish. Descending the actual
determinant contraction through exterior power and tensoring eta yields an
invariant coefficient with basis evaluation one. Fermionic alternation,
right-Weyl invariance and residual phase cancellation are all checked.

Separately, L2 coefficients on the original SM/Higgs-only alphabet vanish at
every derivative-free degree via the composable interface. That field domain
excludes the neutrino/eta extension. Thus this theorem and the dressed witness
have different inputs. A charged scalar can compensate the pair charge; no
universal total-L2 prohibition on an unspecified extended alphabet follows.
Only one selected neutrino copy and eta are admitted, not the full model.

See [reader-facing comparison](../../../../model-studies/flavor-quarticity-controls/results.md),
[frozen contract](../../../../topics/flavor-quarticity-controls/README.md),
and [persistent verification](../../../../topics/flavor-quarticity-controls/verification.md).

## Joint UV Prohibition Consumer

The [representative pattern catalogue](../../../../topics/prohibition-patterns/catalogue.md)
connects these existing DGT dictionaries through
`GUT.ProhibitionPatterns.dgt_uv_baryon` and `dgt_joint`. B1/B2 prohibition for
the UV Circle action follows from the proved restriction to Z9 and preservation
of the underlying coefficient linear map. The same UV group also forbids the
two prescribed dipole transitions. The joint predicate keeps the mixed-field
and dipole domains separate; no full LFV or generated matching claim is added.

## Mixed Prohibition/Allowance Requests

The [mixed-consumer results](../../../../topics/dgt-quarticity-mixed-requests/results.md)
use `GUT.DgtQuarticityMixedRequests.dgt_satisfies` to combine IR B1/B2
prohibition with allowance of each actual selected IR dipole image. The UV
negative control rejects the same selected allowance under Circle.
`quarticity_satisfies` combines SM/Higgs L2 and bare-nuR prohibition with
selected eta-dressed allowance. The dressed nonzero witness prevents adding
prohibition of that same domain. The existing field-action/nonzero certificates
are reused; no common extended-alphabet classification or rate is inferred.
