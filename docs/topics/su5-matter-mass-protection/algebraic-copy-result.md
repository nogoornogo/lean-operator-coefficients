# Algebraic Common-Copy Obstruction With Semisimple Source

## Unified Endpoint

`NonScalarInvariantMass.arbitrary_mass_light_exterior_of_semisimple` applies to
an arbitrary group H on the same actual common-copy carrier
`(Ten tensor S) + bar-five + (Ten tensor T)*`. Its group/action input is
semisimplicity of the source representation s. It assumes no topology on H,
compactness, continuity, target semisimplicity or source/target unitarity.
The subsequent [pure-carrier relaxation](algebraic-carrier-result.md) removes
the model adapter's remaining norm/inner-product interfaces. Both the model
endpoint and shared kernel theorem now use algebraic complex vector spaces.

For arbitrary invariant symmetric complex-bilinear B and dim T < dim S, the
endpoint derives the three residual-equivariant species mass maps, exact
mass-form equality, actual participating-range membership in B's radical, and
a nonzero SM/H/Lorentz/fermionic physical qque exterior coefficient on the
original ranges. The normal form and right-handed dual dictionary are reused
unchanged. The bar-five keeps an independent genuine scalar character psi;
gauge/residual actions remain external products with common copy origin.

This replaces compactness/continuity by an explicit algebraic source condition;
it does not establish an unrestricted arbitrary-group theorem without source
semisimplicity. Existing compact/continuous endpoints remain available and
retain their original signatures.

## Algebraic Common-Kernel Mechanism

[AlgebraicCommonKernel](../../../Math/RepresentationTheory/Decomposition/AlgebraicCommonKernel.lean)
is a reusable module theorem, separate from physics. It uses the actual
isotypic components of the semisimple source over its acting ring. Each component
collects all copies of one simple module type; distinct components are independent
and their direct sum is the whole source.

Suppose each source component admitted an injection into the target by one of
the available mass maps. Images of different components lie in different target
isotypic components. Those target components are independent even though the
target itself need not be semisimple. The component injections therefore assemble
into an injection of the whole source into the target. The positive dimension
difference forbids this.

Consequently there is one source component on which every available mass map
has nonzero kernel. Each restricted kernel is semisimple. A simple submodule
inside it has the component's common simple type. Mapping it back into the
actual source gives a genuine simple submodule of each actual mass kernel.
This is support and actual submodule extraction, not an inference from character
values or a supplied constituent certificate. The module theorem handles any
nonempty indexed family of maps, with three maps used by the qque application.

[AlgebraicCommonCopyKernel](../../../Physics/FieldTheory/Mass/AlgebraicCommonCopyKernel.lean)
converts the module result to residual representations. Each original kernel
is semisimple because it is a subrepresentation of the semisimple source.
Thus each derived simple inclusion has an equivariant retraction. Actual
module equivalences identify all three simple submodules with the same source
type, giving common split constituents. The existing spinor/exterior construction
then produces the physical qque coefficient. No Haar averaging, unitary target
model, character orthogonality or target invariant metric is needed here.

`NonScalarCopyMass.exists_light_exterior_of_semisimple` transports that result
onto original participating ranges. The arbitrary-B endpoint uses the existing
species normal form and exact radical equality to complete the unified theorem.
No normal-form, species-equivariance or light-membership premise is added.

## Boundaries And Verification

The remaining representation restrictions are common factorized copy actions,
source semisimplicity, the current matter carrier, unbroken SM cover invariance
and positive dimension difference. Removing source semisimplicity is not claimed:
nonsemisimple modules need not supply the equivariant retractions used here.
Independent species actions, new matter irreps, the dim T ≥ dim S regime,
whole-light transport, global descent, UV residual mechanisms and all-BNV
protection remain separate questions. An allowed coefficient is not a generated
Wilson coefficient or a decay rate.

The [frozen plan](algebraic-copy-plan.md) owns this phase. Math/Physics audits
cover reusable interfaces; expanded SU(5) audits check the model endpoints and
reject original SU(6) dependencies. See [verification](verification.md) for
focused/full builds and repository checks. No literature input, custom axiom,
pin or proof-limit change is introduced.
