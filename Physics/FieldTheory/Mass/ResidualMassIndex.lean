import Physics.FieldTheory.Mass.ConjugationMassIndex
import Math.RepresentationTheory.Characters.ResidualWeightCharacter

open Math

/-! Actual weightwise residual dual indices after invariant mass removal.
The residual group is not assumed Abelian, and the conjugator need not
preserve the mass or the radical. -/

set_option autoImplicit false

namespace GUT.ResidualMassIndex

noncomputable section

open InvariantWeylMass ResidualWeightSpace ResidualWeightCharacter

variable {T H G E : Type*} [CommGroup T] [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : T →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))

omit [FiniteDimensional ℂ E] in
include hu in
theorem light_torus_unitary :
    UnitaryMultiplicity.IsUnitaryRepresentation (torus B.radical.toRepresentation) :=
  fun t v w => hu t v w

include hu in
theorem weight_index_invariant (a : T ≃* T) (n : G)
    (hc : ∀ t, j (a t) = n * j t * n⁻¹) (chi : T →* Circle) (h : H) :
    index B.radical.toRepresentation (chi.comp a.toMonoidHom) h =
      index B.radical.toRepresentation chi h := by
  apply index_invariant B.radical.toRepresentation (light_torus_unitary j rho B hu) a
  intro t h
  exact ConjugationMassIndex.radical_dual_character_invariant_prod
    j a.toMonoidHom n hc rho B t h

end
end GUT.ResidualMassIndex
