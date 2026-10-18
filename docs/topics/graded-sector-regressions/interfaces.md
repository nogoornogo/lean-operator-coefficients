# Input Dictionaries And The Arbitrary-Flavor Inverse

## Six Quarks

The independent input is `DeltaBTwoModelInterface.ModelSector up down`, on
the sixth exterior power of the physical up/down sum with intrinsic bidegree
`(2,4)`. The group is `(SM gauge × R) × right Weyl`; the graded comparison
reassociates it as `(SM gauge × right Weyl) × R`. Slot order is `u,d,u,d,d,d`.
Right-up/right-down hypercharge weights are `4,-2` in the established integer
convention, cancelling on this content. Integer baryon grade is `6`, hence
physical baryon number two; this does not impose baryon symmetry invariance.

The ordered carrier is `(Color ⊗ right Weyl) ⊗ Flavor(slot)`. The existing
`DeltaBTwoFlavorBridge.reorder` transports physical field order to that order.
Local and residual actions are independent; the comparison must prove equality
with `slotAction`. The local invariant coordinates are 25 entries, subject to
four typed simultaneous flavor/local exchange equations. They are not 25 free
coefficients. The two-probe target applies only to the stated scalar-flavor
one-generation specialization.

Source inspection found an unnecessary finite-dimensional premise in the old
assembly inverse: it expanded flavor vectors in finite bases. The replacement
uses `IndexedTensorSeparation.equiv`, multilinear tensor lifting, and the existing
local reconstruction linear map. Its pure-tensor formula is unchanged.
The targeted rebuild of `DeltaBTwoFlavorBridge` passed 3,287 jobs.
`AuditSixQuarkArbitraryFlavor` passed eight strict transitive axiom checks,
allowing only `propext`, `Classical.choice`, and `Quot.sound`. The full compatibility
rebuild passed at the topic's final acceptance gate; see [results](results.md).

## LLHH

The independent input is `WeinbergSMInterface.ModelSector a`, on
`Λ² Lepton ⊗ Sym² Weak`. The physical local group is SM gauge × left Weyl.
The existing surjective projection to weak × Weyl supplies the already proved
`reducedEquiv`, including hypercharge cancellation. The comparison then uses
singleton lepton/Higgs species alphabets with mixed degree `(2,2)`.

Lepton local carrier is `Weak ⊗ left Weyl`, with arbitrary residual flavor F.
Higgs local carrier is Weak; its residual carrier is ℂ with trivial R action.
The generic Higgs field is `Weak ⊗ ℂ`, identified by tensor-unit removal.
Evaluation on singleton species sums and tensor-unit removal must be equivariant.
The generic residual quotient Hom is compared to the existing
`Hom_R(Sym² F, ℂ)` through the same independent LLHH sector.

Lepton exchange is signed; Higgs exchange is unsigned. Exterior and symmetric
power descent must preserve the original generator evaluation, not introduce
an unexplained factorial. The old polarized contraction and one-generation
normalization provide independent controls. No multi-doublet Higgs model or
dimension-five field-content enumeration is asserted.

## Verification Status

The input dictionaries and both connection modules have passed focused builds,
strict audits and the full compatibility build; see [results](results.md) for
exact commands. This document records conventions, not a new
literature-basis coverage claim.
