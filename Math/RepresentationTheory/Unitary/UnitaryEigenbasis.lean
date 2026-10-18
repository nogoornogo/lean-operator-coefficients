import Math.RepresentationTheory.Characters.UnitaryCharacterProfile
import Mathlib.LinearAlgebra.DirectSum.Basis

/-! Finite eigenbases for unitary group actions. The Abelian character
decomposition is reused on a cyclic restriction for a single group element. -/

set_option autoImplicit false

namespace Math.UnitaryEigenbasis

noncomputable section

open UnitaryCharacterProfile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem exists_character_basis {H : Type*} [CommGroup H]
    (rho : Representation ℂ H E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (n : ℕ) (hn : Module.finrank ℂ E = n) :
    ∃ (b : Module.Basis (Fin n) ℂ E) (chi : Fin n → H →* Circle),
      ∀ h i, rho h (b i) = (chi i h : ℂ) • b i := by
  classical
  let := activeFintype rho hu
  let I := Σ chi : Active rho, Fin (Module.finrank ℂ (space rho chi.val))
  let bi (chi : Active rho) := Module.finBasis ℂ (space rho chi.val)
  have hi : DirectSum.IsInternal (fun chi : Active rho => space rho chi.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr (internal rho hu)
  let b : Module.Basis I ℂ E := hi.collectedBasis bi
  have hc : Fintype.card I = n := (Module.finrank_eq_card_basis b).symm.trans hn
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hc
  refine ⟨b.reindex e, fun i => (e.symm i).1.val, ?_⟩
  intro h i
  have hm : b (e.symm i) ∈ space rho (e.symm i).1.val := hi.collectedBasis_mem bi _
  simpa only [Module.Basis.reindex_apply] using hm h

theorem exists_element_basis {G : Type*} [Group G]
    (rho : Representation ℂ G E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (g : G) (n : ℕ) (hn : Module.finrank ℂ E = n) :
    ∃ (b : Module.Basis (Fin n) ℂ E) (w : Fin n → Circle),
      ∀ i, rho g (b i) = (w i : ℂ) • b i := by
  let c : Multiplicative ℤ →* G :=
    { toFun := fun k => g ^ Multiplicative.toAdd k
      map_one' := zpow_zero g
      map_mul' := fun j k => zpow_add g _ _ }
  obtain ⟨b, chi, he⟩ := exists_character_basis (rho.comp c) (fun h => hu (c h)) n hn
  refine ⟨b, fun i => chi i (Multiplicative.ofAdd 1), ?_⟩
  intro i
  have hh := he (Multiplicative.ofAdd 1) i
  change rho (g ^ (1 : ℤ)) (b i) = (chi i (Multiplicative.ofAdd 1) : ℂ) • b i at hh
  simpa only [zpow_one] using hh

end

end Math.UnitaryEigenbasis
