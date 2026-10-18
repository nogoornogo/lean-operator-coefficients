# Arbitrary Invariant Mass And Common Non-Scalar Copy Representations

## Two Completed Statements And Their Intersection Boundary

The two source statements remove different assumptions. The first starts with
arbitrary invariant symmetric mass and retains common scalar chi. The second
allows common non-scalar copy representations and retains the three equivariant
species mass-map presentation. No single theorem here removes both assumptions
simultaneously. The subsequent [unified theorem](unification-result.md) closes
that bridge; the preceding two statements retain their original hypotheses. Their exact endpoints
are actual light participating fields and a physical qque exterior coefficient.

## 1. Derived Species Dirac Normal Form

[InvariantMassNormalForm](../../../GUT/SU5/SelectionRules/InvariantMassNormalForm.lean)
retains actual p tens, one bar-five and q dual tens, standard SU(5) branching,
common scalar chi on tens and an independent bar-five psi. B is an arbitrary
SM-cover x H invariant symmetric complex-bilinear form. H is Abelian here,
without finite or topological assumptions. B is not assumed to be `ofDirac`.

The charge-separation lemmas derive vanishing of all same-side bilinear blocks
from actual branching: source charges (-4,1,6,2,-3), target-dual charges
(4,-1,-6). No opposite pair exists within either side. Thus Majorana candidates
are admitted initially and proved absent for this carrier under unbroken SM
invariance; Majorana masses are not excluded by a definition. A fixed circle
phase pi/16 separates the bounded charges, avoiding the historical SU(6)
circle-lattice dependency without relaxing the import-origin audit.

[BipartiteNormalForm](../../../Physics/FieldTheory/Mass/BipartiteNormalForm.lean)
derives `crossMap` by bidual evaluation of B's cross block. It proves equality
of B with the symmetric evaluation mass of that map. The hypotheses of its
reusable theorem are no same-side pairings; the actual SU(5) adapter proves
these hypotheses rather than supplying them as new model certificates.

The SM Schur classification is also derived. Q/up-left/electron-left are
proved irreducible with dimensions 6/3/1. Different-dimensional off-diagonal
intertwiners vanish, while endomorphisms are scalar. `ten_endomorphism` proves
every SM-equivariant ten endomorphism is one of the species-weighted maps.
The bar-five-to-ten block vanishes by hypercharge separation. Copy entries
therefore extract three complex q-by-p matrices. `massMap_eq` reconstructs
the full map, and `matrix_normal_form` proves B's form equals the earlier
`MatrixTenMass.mass` for the derived matrices.

`arbitrary_mass_light_exterior` applies that exact equality: when q < p,
actual participating species lie in B's radical and support a nonzero physical
SM/H/Lorentz/fermionic qque exterior coefficient. No Dirac ansatz, maximum
rank, shared copy direction or supplied light-membership premise remains in
this scalar-copy theorem. New singlets, further matter irreps and electroweak
breaking are outside its carrier and invariance conditions.

## 2. Common Non-Scalar Copies And Actual Kernels

[CommonCopyKernel](../../../Physics/FieldTheory/Mass/CommonCopyKernel.lean)
takes common finite-dimensional source/target representations s on S and t
on T of a compact topological group H, with jointly continuous actions and
unitary target t. S/T have the stated finite-dimensional inner-product
interfaces. H need not be Abelian; finite groups with the discrete topology
are included when these action/unitarity interfaces are supplied. Scalar
characters, common irreducible S/T, full rank and an assumed kernel
constituent are not required.

For arbitrary three intertwiners Mq/Mu/Me : s → t, character exactness gives
kernel character minus the actual unitary target-range complement character
as `character(s)-character(t)`. A normalized presentation of the actual source
and target character difference is constructed using repository theorems.
Positive dimension difference selects a positive irreducible coefficient.
The same constituent is then extracted as an actual split subrepresentation
of all three kernels. The virtual character is used to derive these actual
splits, not substituted for light fields.

`kernel_physical_exterior` uses the existing symmetric evaluation and spinor
exterior construction. This is a genuine nonzero physical coefficient, with
its existing matched witness, on the standard gauge species tensored with
actual kernel multiplicities. Right-handed up/electron use kernel duals.
H acts trivially on spinors.

[NonScalarCopyMass](../../../GUT/SU5/SelectionRules/NonScalarCopyMass.lean)
constructs actual matter `(Ten tensor S) + bar-five + (Ten tensor T)*` and
the symmetric species Dirac mass from Mq/Mu/Me. The bar-five uses a genuine
scalar character psi for any H. Gauge and residual actions are genuine external
products, preserving the common copy-representation origin across species.
The actual ten branching maps tensored with kernel inclusions give derived
injective equivariant Q/up-left/electron-left maps. All their images lie in
the actual mass radical. Range representations agree with actual restricted
actions. Dual tensor and bidual equivalences prove the right-handed dictionary.
`exists_light_exterior` transports the physical coefficient onto these actual
participating ranges when dim T < dim S.

This is a factorized common-copy action, not the general gauge-compensated
noncommuting UV action from the earlier scalar/block phase. Independently
varying species actions are outside this theorem. No coefficient on the whole
untyped light carrier, exact complete SM spectrum, full UV scalar/VEV model,
generated Wilson coefficient or rate is asserted.

## Verification And Endpoint

The [frozen plan](normal-form-copy-plan.md) owns these stages. Reusable strict
transitive audits cover both shared physics modules and both SU(5) applications;
the SU(5) audits reject original SU(6) import origins. Dependency pins and
standard axiom allowances are unchanged. Commands and final results are in
[verification](verification.md). Remaining general connections are explicit
rather than silently added to either theorem's hypotheses.
