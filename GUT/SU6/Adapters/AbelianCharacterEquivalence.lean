import GUT.SU6.Adapters.AbelianCharacterBasis

open Physics

/-! Equal trace characters give actual equivalences of finite-dimensional
unitary Abelian representations, via the proved prescribed eigenbases. -/

set_option autoImplicit false

namespace GUT.AbelianCharacterEquivalence

noncomputable section

open UnitaryVirtualRealization AbelianCharacterBasis

variable {G : Type*} [CommGroup G]

def ofCharacter (R S : ActualUnitaryGroupRepresentation G)
    (h : ∀ g, R.rho.character g = S.rho.character g) :
    Representation.Equiv R.rho S.rho := by
  let ht : ∀ g, S.rho.character g = ∑ i, label R i g :=
    fun g => (h g).symm.trans (character_sum R g)
  let b := prescribedBasis S (label R) ht
  let e := (basis R).equiv b (Equiv.refl _)
  refine Representation.Equiv.mk e (fun g => ?_)
  apply (basis R).ext
  intro i
  change e (R.rho g (basis R i)) = S.rho g (e (basis R i))
  rw [basis_action, map_smul]
  have he : e (basis R i) = b i := Module.Basis.equiv_apply _ _ _ _
  rw [he, prescribedBasis_action]

end

end GUT.AbelianCharacterEquivalence
