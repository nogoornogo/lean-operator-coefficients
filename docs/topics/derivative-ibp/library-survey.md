# Lean Library Survey And Verification Boundary

## Fixed Local Environment At Survey Checkpoint

The later authorized [dependency integration](dependency-integration.md) records
the current v4.35.0 environment. The checks below retain their original pins.
The later [scalar implementation](../../proof/current/core/Math/SCALAR_JET_IBP.md)
uses the current Mathlib derivation/grade APIs and the repository's quotient
descent; its implemented theorems and strict audits are separate from these
original library-name probes.

- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `1a547d8a48a8fa7877d2decb69d7294723bb0187`.
- TauCeti: `b9e2e182804073eb92718b68a9baf37df8e189bd`.
- No dependencies or pins changed; no new proof definitions were implemented.

Source searches used `rg --files` and `rg`, followed by relevant source reads.
Search terms included derivative/derivation, jet/jet bundle, total derivative,
IBP/integration by parts, weighted homogeneous, Koszul, and variational bicomplex.
A name match alone was not classified as the required EFT foundation.

## Reusable Local Interfaces

| Need | Existing source/API | What is supplied; what remains |
| --- | --- | --- |
| Derivation from generator values | Mathlib `Algebra/MvPolynomial/Derivation`: `mkDerivation`, `mkDerivation_X`, `derivation_ext` | Polynomial Leibniz rule and extensionality, with arbitrary variable types. Jet-index shifts and their interpretation remain to be defined. |
| Commutation proof | Mathlib `RingTheory/Derivation/Lie`: `Derivation.commutator_apply` | The bracket is a derivation; vanishing on generators can help prove commuting total derivatives. No jet commutation theorem is supplied by this API alone. |
| Field/derivative grading | Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous`: `IsWeightedHomogeneous`, `weightedHomogeneousSubmodule`, `weightedHomogeneousComponent`, `sum_weightedHomogeneousComponent` | Monoid-valued weights and decomposition, allowing joint field/derivative grades. Preservation/shift under the proposed D must be proved. |
| Finite homogeneous components | `MvPolynomial.weightedHomogeneousSubmodule_fg` | Requires a finite variable type and nonzero natural weights. It does not directly prove finiteness of infinite jet variables or a derivative-only grading with undifferentiated weight-zero fields. |
| Coordinates versus basis-free bosons | Mathlib `LinearAlgebra/SymmetricAlgebra/Basis`: `SymmetricAlgebra.equivMvPolynomial` | Algebra equivalence after choosing a basis; differential and representation compatibility remain obligations. |
| Exterior/statistics constructors | Mathlib `ExteriorAlgebra.lift`, `ExteriorAlgebra.map`; project `ExteriorLeftDerivative.leibniz` | Algebra construction and odd Grassmann contraction. The existing odd contraction is not the even spacetime derivative. |
| Symmetric representations | TauCeti `RepresentationTheory/SymmetricPower`: `Representation.symmetricPower` | Group action on each symmetric power. It does not construct jet shifts or an IBP relation map. |
| Stable linear relation quotient | Project `RelationQuotient.equiv`, `relations_stable` | Exact descent for invariant functionals once the relation source and stability are proved. |
| Local action and residual Hom | Project `LocalRelationHom.equiv`; `GradedMixedCompleteness.equiv` | Existing quotient/Hom and derivative-free grading connections. IBP mixes derivative distributions, requiring a new connection rather than a mere renamed content. |
| Analytic IBP | Mathlib `Analysis/Calculus/LineDeriv/IntegrationByParts`: `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable` | Genuine integral identity with normed-space, Haar-measure, differentiability and integrability hypotheses. Not a presentation or completeness proof for formal IBP relations. |

TauCeti's weighted-homogeneous substitution and analytic directional IBP files
were also inspected. Its `KoszulTensor` supplies a graded sign automorphism,
not the translation complex or exactness needed to count EFT IBP classes.
Generic homological bicomplex constructors likewise do not identify the desired
horizontal differential. No ready complete EFT jet/IBP-to-residual-Hom bridge
was found in the bounded local pass; this is not a theorem of library-wide absence.

## Successful Local Elaboration Probe

A disposable `/tmp/derivative-ibp-library-probe.lean` imported the following
modules and checked 19 existing names with `#check`; `lake env lean` exited zero
without warnings. This records APIs, not a new theorem or full-build baseline.

```lean
import Math.RepresentationTheory.LocalRelationHom
import Math.RepresentationTheory.GradedMixedCompleteness
import Math.LinearAlgebra.ExteriorLeftDerivative
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.RepresentationTheory.SymmetricPower
#check MvPolynomial.mkDerivation
#check MvPolynomial.mkDerivation_X
#check MvPolynomial.derivation_ext
#check Derivation.commutator_apply
#check MvPolynomial.IsWeightedHomogeneous
#check MvPolynomial.weightedHomogeneousSubmodule
#check MvPolynomial.weightedHomogeneousComponent
#check MvPolynomial.sum_weightedHomogeneousComponent
#check MvPolynomial.weightedHomogeneousSubmodule_fg
#check SymmetricAlgebra.equivMvPolynomial
#check ExteriorAlgebra.lift
#check ExteriorAlgebra.map
#check Math.ExteriorLeftDerivative.leibniz
#check Representation.symmetricPower
#check Math.RelationQuotient.equiv
#check Math.RelationQuotient.relations_stable
#check Math.LocalRelationHom.equiv
#check Math.GradedMixedCompleteness.equiv
#check integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
```

The checked quotient equivalence needs the supplied stable relation submodule;
it proves no premise identifying that submodule with actual divergences.

## External Physlib: More Than A Search Lead

See the pinned [external source register](references.md#l1--external-physlib-snapshot).
The recursive tree was complete (`truncated = false`). The two general
`PhyslibAlpha/Mathematics/ExteriorAlgebra.lean` and `SymmetricAlgebra.lean` files
were downloaded to `/tmp/derivative-ibp-physlib/` without changes and each checked
with `lake env lean <file>`. Both commands exited zero without warnings under
the local pins, despite the external project's different toolchain/Mathlib pins.
They import only Mathlib modules, so these two tests needed no Physlib installation.

The following selected theorems were then checked with `#print axioms` appended
to disposable copies of those unchanged sources:

| Namespace | Checked suffixes |
| --- | --- |
| `ExteriorAlgebra` | `derivationOfLinear_ι`, `derivationOfLinear_mul`, `derivationOfLinear_comm_apply`, `exteriorAlgebra_derivationOfLinear` |
| `SymmetricAlgebra` | `derivationOfLinear_ι`, `derivationOfLinear_mul`, `derivationOfLinear_comm_apply`, `symmetricAlgebra_derivationOfLinear` |

All eight reports list only `propext`, `Classical.choice`, `Quot.sound`.
These are genuine transitive axiom reports on selected existing external
lemmas, not audits of our future integration or all external source files.
No downloaded source or generated output is committed.

These APIs supply even derivations extending linear maps, their generator and
Leibniz formulas, commutation from commuting generator maps, and covariance
for families whose directions mix under the group action. They directly
address an important part of the previously estimated mixed-statistics cost.
Their names, source ownership and API shape would still need project-specific
adaptation and persistent audits before use in Math-owned code.

The full SM jet derivative and analytic first-variation packages were source
inspected only. Their imports, model conventions and compatibility were not
built. They do not supply a verified bridge to this repository's content
quotients. No claim about all Physlib sources or absence of other relevant
external Lean projects is made.
