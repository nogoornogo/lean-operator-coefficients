# Candidates 7 and 8: concrete source-admission recheck

The bridge proofs at checkpoint 01 were verified implications. That checkpoint did
not establish all their premises for a complete literature model. This recheck
compares those premises with the selected concrete sources and records the
remaining model-level obligations without calling them verified.

## Candidate 7: conventional charge-two B-L

Re-read [1411.5042v2](https://arxiv.org/abs/1411.5042v2), introduction pp.1–3,
especially the conventional nuR charge -1 discussion and chi2 charge +2.
This is the paper's conventional comparison, not its alternative (+5,-4,-4)
model or subsequent S3 construction. The already selected variant is unchanged.

| Required item | Recheck result |
| --- | --- |
| Integer normalization X=3(B-L) | Matches conventional charges: physical quarks +1, leptons -3, singlet VEV +6 |
| Nonzero singlet VEV | Explicit breaking-stage assumption; the Lean stabilizer theorem covers every nonzero value, not just a chosen numerical sample |
| Residual subgroup and all signed SM field actions | Closed by BLResidualRestriction embedding/range/stabilizer and actual-field restriction theorems |
| Higgs/dual action | Neutral; actual field restriction checked |
| B1 coefficient conclusion on declared restricted SM alphabet | Attained minimum dimension six and its universal lower bound are proved on the restricted action itself |
| Exact UV light mass radical and removal of all sterile modes | Not verified: no particular full-rank neutrino Yukawa/mass input was supplied or derived |
| Whole-model admission | Not certified; successful result is the declared SM restriction with nonzero-VEV premise |

Thus the source-to-residual-action part of this candidate is checked. A claim
that *exactly* the original SM alphabet exhausts the UV massless states would
require its own mass/kernel proof and a nondegeneracy condition. Merely having
a permitted Majorana term does not prove invertibility. That stronger claim
is neither needed for the restricted coefficient result nor asserted here.

## Candidate 8: Heeck–Patra triplet-breaking LR input

Re-read [1507.01584v3](https://arxiv.org/html/1507.01584v3), Section II Eqs.(1)–(3)
and footnote 1: the fermion charges, neutral bidoublet, charge-minus-two right
triplet and its nonzero neutral VEV. These are the representation/breaking
inputs selected in the original pass. They do not provide the explicit
quadratic-column identity required by LRLightHiggs.kernel_of_coordinates.
No concrete scalar-potential parameter point establishing that identity was
identified in this selected source input.

| Required item | Recheck result |
| --- | --- |
| LR bidoublet and residual charges | Match declared source input; LRLightHiggs constructs its actual group representation |
| SM column decomposition and standard-Higgs map | Proved, including injection/retraction, actual action and dual convention |
| Pure-X residual action | Neutral on bidoublet; negative-charge VEV is fixed |
| A complete single light-doublet kernel | Proved only under the explicit quadratic-coordinate/eigenvalue premise |
| That premise for a source-specified potential/parameter point | Not verified; the necessary input is absent from the selected model contract |
| Whole-model single-Higgs admission | Unresolved, not a verified application of the conditional kernel theorem |

## Formal sufficiency controls

[LRModelAdmissionControls](../../../GUT/Common/ProtonProtection/LRModelAdmissionControls.lean)
checks three exact quadratic operators on the actual declared bidoublet:

- (heavy,light)=(1,0): the kernel is exactly the selected Higgs image.
- (1,1): the operator is the identity, its kernel is zero and differs from
  the selected nonzero Higgs image. It respects even the full LR action.
- (0,0): the kernel is the entire bidoublet.

`selection_not_universal` proves that SM-equivariance alone cannot imply the
selected kernel. The residual action is fixed and neutral throughout. These
are controls of the representation-to-selection inference, not constructions
of full scalar potentials or counterexamples to the paper's physical results.
No claim is made that these quadratic operators satisfy every other model
condition, including a specified vacuum, potential or fermion spectrum.

## Outcome and required next input

The requested model applicability check is performed and recorded; it does
not turn either candidate into a full UV model certificate. Candidate 7's
residual/action application is closed on the declared SM fields. Candidate 8
still has a specific unverified source-admission premise: a scalar potential
and parameter choice yielding the stated single-light-doublet operator, or an
explicit different light-subspace identification. The source/representation
data alone do not discharge that premise. Its conditional result is retained.

A further UV-spectrum check of candidate 7 additionally needs the neutrino
mass input/nondegeneracy and a declared pre-EW mass dictionary. Constructing
those inputs is separate from rerunning the existing bridge audit. No source
conclusion has been promoted to an axiom or a verified premise.

See [verification](model-admission-verification.md). This bounded recheck stops
at these identified missing model inputs; no foundation or potential was added.
