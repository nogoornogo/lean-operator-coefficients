# Full SM Higgs Coefficient Connection

## Exact endpoint

For every pair of natural Higgs degrees h,d and an arbitrary supplied source
representation a of the full gauge/Weyl/residual group Gamma, the original
fixed-content coefficient space now has constructed linear equivalences

    original full-field coefficients at scalar content (h,d)
      equiv Hom_Gamma(a tensor (Sym^h H tensor Sym^d Hdual), C)
      equiv Hom_Gamma(a tensor Pi_r constituent_r, C).

The finite constituent index is 0 <= r <= min(h,d). Its actual Gamma action is

    constituent_r = chi^h * chi^(-d) twist
      (Sym^(h+d-2r) doublet pulled back along the weak projection).

For the existing SM Higgs, chi(g) is the hypercharge-circle phase z^3.
The source retains all color, Weyl, hypercharge and residual constraints.
No source weak-triviality, semisimplicity, finite dimension, seed, mass or
supplied content equivalence is a premise of these connections. The two
remaining presentation/action obligations from the preceding checkpoint
are complete for the specified one-Higgs/dual input.

## Full field content is checked

[TwoSpeciesPattern](../../../Math/RepresentationTheory/TwoSpeciesPattern.lean)
constructs the canonical pattern with h occurrences of species zero and d
of species one. Every pattern-preserving permutation decomposes into an
independent permutation of each block. `orbit_iff_counts` proves that a word
is in the pattern orbit exactly when its two species counts are h and d.

[TwoSpeciesSymmetricDescent](../../../Math/RepresentationTheory/TwoSpeciesSymmetricDescent.lean)
constructs the dependent typed slot reindexing, including the necessary
species type transports. It proves pattern compatibility iff independent
symmetry in the two blocks. Both symmetric quotients are descended, with
inverse identities, to obtain the split tensor carrier's linear functionals.
The fields in the two blocks may have different module types.

[TwoSpeciesCoefficientBridge](../../../Math/RepresentationTheory/TwoSpeciesCoefficientBridge.lean)
proves actual group covariance in both directions and joins this equivalence
with the previously proved full-field typed pattern reconstruction. Its
`sourceEquiv` retains a supplied source's already imposed statistics through
dual-valued currying. No raw ordered tensor is assumed to survive descent.
Stabilizer normalization and both inverse identities are retained.

## Other actions are retained

[CharacterTwistTransport](../../../Math/RepresentationTheory/CharacterTwistTransport.lean)
proves actual equivalences for dual, symmetric and tensor character twists.
For any group homomorphism j:Gamma -> SU2 and scalar character chi:Gamma -> Cunits,
[TwistedSU2ClebschGordan](../../../Math/RepresentationTheory/TwistedSU2ClebschGordan.lean)
transports the proved SU2 decomposition with the common character
chi^h * chi^(-d) on every constituent. No full-group compatibility certificate
is supplied in place of that proof.

[SMHiggsConstituents](../../../Physics/StandardModel/Operators/SMHiggsConstituents.lean)
constructs the actual weak and hypercharge projections of the existing SM
gauge/Weyl/residual group. It proves that the original Higgs action equals
the pulled-back, character-twisted doublet, then derives its actual full-group
constituent equivalence. `common_charge` retains the exact hypercharge phase
factor. Color, Weyl and residual factors are trivial on this selected Higgs
input; their actions on the fermion source are not discarded.

## Original SM consumer

[FullHiggsCoefficientBridge](../../../Physics/StandardModel/Operators/FullHiggsCoefficientBridge.lean)
uses the original `BnvMixedInput` scalar fields H tensor C and Hdual tensor C
with neutral one-dimensional scalar multiplicities. It constructs their
individual representation equivalences to the actual doublet and dual.

- `mem_space_iff` identifies the selected full subspace with vanishing on
  every scalar word whose counts differ from (h,d), for every source vector.
- `splitEquiv` connects that space to the actual independently symmetric
  SM Higgs/dual coefficient space.
- `constituentEquiv`, `allowed_iff` and `forbidden_iff` transport it to the
  full-group constituent coefficient space.
- `matterEquiv` instantiates the source with every exterior degree of the
  actual ten signed SM fields and their supplied flavor representations.
- `weakSinglet_allowed_iff` now applies the preceding weak-singlet criterion
  to the original full carrier: allowance iff h=d and the source invariant
  Hom is nonzero. This corollary explicitly requires whole-source weak
  triviality; the general bridge does not.

The supplied flavor representations can be the fixed three-generation input.
No new UV model or field-realization premise is introduced.

## Remaining support work

This is a full coefficient-space connection at each h,d. Its finite
constituent list grows with the degrees; no uniform bound over all h,d is
claimed. A classification of the surviving source/constituent Hom factors
for every selected fermion content still needs its own proof. Missing such
a proof is not evidence of prohibition. These connections do not alone
complete the fixed-input SM support classification.

The subsequent [finite reduction](../sm-higgs-support-cutoff/results.md)
adds the actual statistical-source weak bound, degree-independent finite Hom
table and support stabilization. Its Hom predicates remain unclassified for
arbitrary residual action classes;
the earlier per-degree endpoint and verification baseline remain separate.

For the existing cyclic q/l residual actions, the later
[compact local-kernel completion](../sm-compact-kernel-completion/results.md)
classifies those retained predicates by an exact finite matrix-rank condition.
It does not extend that classification to arbitrary residual action classes.

Multiple Higgs copies, arbitrary non-scalar residual actions on Higgs fields,
derivatives/EOM/IBP, quantum protection, UV realization, VEVs, masses, matching
and rates remain outside this endpoint. The generic character transport can
handle a scalar residual Higgs character; the actual SM consumer here uses
the specified neutral scalar flavor action.

The [verification record](verification.md) records strict audits and repository
checks. Work remains on the approved topic branch; no master merge or push is
authorized.
