# Complete Qque Coefficient Classification

The final endpoint is proved: the independently defined degree-(2,1,1)
SM-cover x H x SL(2,C)-invariant exterior sector is linearly equivalent to
`Hom_H(Sym^2 A, B tensor D)`. The details below retain the earlier milestones;
their formerly open surjectivity obligation is closed by the final section.

## Proved

[QqueCoefficientAssembly](../../../Physics/StandardModel/Operators/QqueCoefficientAssembly.lean)
takes arbitrary complex H representations a, b, d, with no compactness,
continuity, finite-dimensionality, positivity or split-quotient premise.
Its residual coefficients are invariant functionals on
`(A tensor A) tensor (B.dual tensor D.dual)`.

`Symmetric` requires exchange symmetry in the two A slots.
`assembleLinear` contracts the existing standard gauge and spinor tensors
and alternates on the whole field sum. A fixed gauge/spinor probe evaluates to

```text
f(x,y,u,e) + f(y,x,u,e).
```

On symmetric f this is twice the original coefficient. Consequently:

- `injective_on_symmetric` separates any two symmetric residual coefficients.
- `symmetricAssembly_injective` expresses this as an injective linear map.
- `assemble_nonzero_iff` proves nonzero descent exactly for nonzero symmetric f.
- `exists_on_fields` transports arbitrary such f through supplied actual-field
  equivalences, without requiring the particular pairwise evaluation construction.

[SymmetricSquareDescent](../../../Math/RepresentationTheory/SymmetricSquareDescent.lean)
uses the existing symmetric-power quotient from mathlib/TauCeti. `equiv`
identifies maps from that quotient with symmetric two-variable multilinear maps.
`equivariantEquiv` restricts this to H-equivariant maps, for any abstract group H.
No finite-dimensionality or topology is needed for this universal property.

## Residual Hom And Independent Sector

[QqueResidualHom](../../../Physics/StandardModel/Operators/QqueResidualHom.lean)
now proves the linear equivalence between symmetric residual functionals and
`Hom_H(Sym^2 A, B tensor D)`. Its math helpers are
[InvariantTensorCurry](../../../Math/RepresentationTheory/InvariantTensorCurry.lean)
and [TensorSquareMultilinear](../../../Math/RepresentationTheory/TensorSquareMultilinear.lean).
Only B and D need finite-dimensionality for tensor duality; H is arbitrary,
and no topology, compactness or constituent premise is imposed. `assembly`
is linear and injective, `assembly_nonzero_iff` preserves nonzero coefficients,
and `exists_on_fields` transports any nonzero Hom element through actual-field
equivalences. No actual-field decomposition is derived by this algebraic API.

[FourSlotSpeciesDegree](../../../Math/RepresentationTheory/FourSlotSpeciesDegree.lean)
defines degree (2,1,1) by independent scaling of the three field summands:
scaling by r,s,t multiplies the exterior coefficient by `r*r*s*t`.
This definition quantifies over all scalars and all exterior vectors and is
independent of the assembly map or any contraction certificate.
[QqueCoefficientSector](../../../Physics/StandardModel/Operators/QqueCoefficientSector.lean)
specializes this to spinor fields. Every assembled qque coefficient belongs
to this sector, and `fromHom_injective` embeds the residual Hom space into the
independently specified, fully invariant sector.

## Ordered Reconstruction And Spinor Uniqueness

[FourSlotSpeciesRestriction](../../../Math/RepresentationTheory/FourSlotSpeciesRestriction.lean)
proves that an exterior coefficient of species degree (2,1,1) is determined
by its ordered Q,Q,U,E slot values. Independent species scaling by 2,3,5
annihilates all other degree-four species patterns. The finite permutation
step is checked by Lean's kernel, not by an external computational oracle.

[FourSlotRestrictionLift](../../../Math/RepresentationTheory/FourSlotRestrictionLift.lean)
constructs the ordered equivariant restriction and proves

```text
alternation ((1/2) * restriction f) = f.
```

The factor 1/2 follows from the two repeated Q slots and the repository's
unnormalized alternation convention. These theorems require no compactness,
continuity or finite-dimensionality. `QqueCoefficientSector.exists_ordered`
exposes the reconstruction for the independently defined spinor-field sector.
This is surjectivity from all invariant ordered field coefficients, not yet
from symmetric residual coefficients.

[WeylSpinorUniqueness](../../../Physics/FieldTheory/Spinor/WeylSpinorUniqueness.lean)
proves `eq_smul_four`: every invariant functional on two left and two right
Weyl spinors is its 0101 basis value times `WeylSpinor.four`. A concrete complex
diagonal element kills twelve of the sixteen basis coefficients; a real
shear gives the sign relations for the other four. Both elements belong to
SL(2,C) by checked determinant proofs. The result concerns all invariant
functionals, not only assembled ones. No additional uniqueness premise or
Lorentz-cover classification is used.

## Boundary At The Third Milestone

The full exterior coefficient space in the old API is not restricted by
definition to qque species degree. The new sector supplies that restriction,
but surjectivity still requires showing that every gauge/spinor invariant
coefficient in it factors through the standard contraction. Ordered
reconstruction and isolated spinor uniqueness are now proved. The inspected
`SMEpsilonTensor` proofs establish gauge invariance of epsilon contractions,
not their uniqueness. Color/weak uniqueness and factorization with arbitrary
gauge/flavor spectators remain open. In particular, the new ordered surjection
does not by itself prove surjectivity of `QqueCoefficientSector.fromHom`.
Those intermediate results did not yet establish exhaustiveness or a
necessary-and-sufficient test. Exhaustiveness is now proved below. A stabilizer
classification remains outside the bounded task.

No old theorem inputs, physical scope, dependency pins or axiom policies changed.

## First Milestone Verification

- `lake build Physics.StandardModel.Operators.Audit.AuditQqueCoefficientAssembly`:
  passed; eight transitive checks allow only propext, Classical.choice, Quot.sound.
- `lake build`: passed, 5743 jobs; existing dependency warnings remain.
- `python3 tools/qque/audit_one_generation.py`: four exact tests passed.
- `python3 tools/qque/audit_pairwise.py`: three exact tests passed.
- `node tools/layout/check-layout.mjs`: 692 modules passed.
- `node tools/docs/check-links.mjs`: 281 Markdown files, 1590 links,
  33 fragments, zero errors.
- `git diff --check`: passed.

The existing computational tests check contraction/sign conventions in their
specified finite controls, not completeness for arbitrary multiplicities.

## Second Milestone Verification

- Focused `AuditQqueCoefficientAssembly` build: eighteen strict transitive
  axiom checks passed with the unchanged allowlist.
- `lake build`: passed, 5748 jobs; no new warnings in the added modules.
- Both qque computational scripts rerun: four plus three exact tests passed.
- Layout: 697 modules passed.
- Documentation links: 281 Markdown files, 1595 links, 33 fragments, zero errors.
- `git diff --check`: passed.

At the second milestone this was still an in-progress topic.

## Third Milestone Verification

- `lake build Math.RepresentationTheory.FourSlotRestrictionLift`: passed.
- Focused `AuditQqueCoefficientAssembly` build: 25 strict transitive axiom
  checks passed; only propext, Classical.choice and Quot.sound are permitted.
- `lake build`: passed, 5751 jobs; existing dependency warnings remain,
  with no new warnings in the added modules.
- Both existing qque computational scripts rerun: four plus three exact tests
  passed. They check the existing sign/nonzero controls, not full surjectivity.
- Layout: 700 modules passed.
- Documentation links and `git diff --check`: passed.

At the third milestone the topic remained on its working branch without a merge.

## Final Classification

[SMEpsilonUniqueness](../../../Physics/StandardModel/Gauge/SMEpsilonUniqueness.lean)
proves uniqueness of invariant bilinear SU(2) and trilinear SU(3) contractions,
using the existing explicit special-unitary elements.
[QqueGaugeUniqueness](../../../Physics/StandardModel/Gauge/QqueGaugeUniqueness.lean)
combines them into `eq_smul_qque`: every ordered gauge coefficient is a scalar
multiple of the standard qque gauge tensor.

[ExternalInvariantFactorization](../../../Math/RepresentationTheory/ExternalInvariantFactorization.lean)
factors an external invariant through a unique contraction with arbitrary
spectator representations. Its applications
[QqueSpinorFactorization](../../../Physics/StandardModel/Operators/QqueSpinorFactorization.lean)
and [QqueGaugeFactorization](../../../Physics/StandardModel/Gauge/QqueGaugeFactorization.lean)
remove spinor and gauge factors without a compactness or continuity premise.

[QqueCoefficientCompleteness](../../../Physics/StandardModel/Operators/QqueCoefficientCompleteness.lean)
constructs the residual coefficient from half the ordered restriction of any
independent-sector coefficient. `residual_symmetric` derives Q-slot symmetry
from alternation and the gauge/spinor signs. `reconstruct` returns the original
exterior coefficient. These give `fromHom_surjective` and the linear equivalence
`equiv`. No decomposition of the sector as an assembly image was assumed.

[FourSlotSpeciesTransport](../../../Math/RepresentationTheory/FourSlotSpeciesTransport.lean)
transports the independent sector through species-preserving equivariant
identifications. `onFieldsEquiv` applies it to actual participating fields.
`exists_on_fields_iff` gives the nonzero-Hom criterion, and
`hasNonzeroAlternation_iff` connects the older sufficient-condition endpoints
without changing their hypotheses.

### Exact Inputs And Scope

- H is any abstract group acting complex-linearly on A, B, D.
- B and D are finite-dimensional only for the final dual-tensor/Hom
  identification. A need not be finite-dimensional in this algebraic API.
- No target positivity, semisimplicity, conjugation, mass, topology or
  compactness is assumed by the classification.
- Actual-field transport supplies SM x H identifications with
  `quark tensor A`, `upRight tensor B.dual`, `electronRight tensor D.dual`.
  It does not derive those identifications or H from an arbitrary model.
- The independently specified sector has species degree (2,1,1) and uses
  the repository's gauge and Weyl-spinor actions, with no derivatives.
  Other field species, other baryon-violating classes, EOM/IBP quotients,
  dynamics, stabilizer classification and an executable general Hom solver
  are not conclusions of this task.

Thus common/pairwise constituents remain sufficient routes, not necessary
conditions. The necessary-and-sufficient condition here is the full symmetric
square Hom, for the specified participating field spaces.

## Final Verification

- Focused `AuditQqueCoefficientAssembly` build: 41 strict transitive axiom
  checks pass with only propext, Classical.choice and Quot.sound allowed.
- `python3 tools/qque/audit_contraction_uniqueness.py`: three exact tests
  check epsilon invariants and rational ranks for the explicit finite sets
  of weak, color and spinor transformations. Complex invariant nullity is
  one in each case. This supplements the Lean proofs; it does not classify
  arbitrary multiplicities or replace a theorem by a computational premise.
- Existing one-generation and pairwise scripts: four plus three tests pass.
- Layout: 707 modules pass; dependency pins and audit policy are unchanged.
- `lake build`: passes, 5758 jobs. Existing dependency warnings remain; no new
  warnings occur in the added proof modules.
- Documentation links: 281 Markdown files, 1609 local links, 33 heading
  fragments, zero errors. `git diff --check` passes.

The complete endpoint is ready for integration into the recorded target
`master`; the target is still the original base commit. Git ancestry records
the actual merge, and the working branch is retained.
