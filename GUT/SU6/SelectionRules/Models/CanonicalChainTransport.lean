import GUT.SU6.SelectionRules.Models.PhysicalChainSource

open Physics

open Math

/-! Keep dependent field transports behind a constructed certificate, as
in EquivariantWeylMassTransport. Every field below is proved by descent;
the certificate is not an additional premise of the legacy-model adapter. -/

set_option autoImplicit false

namespace GUT.SU6.CanonicalChainTransport

noncomputable section

open UnitaryVirtualRealization InvariantWeylMass FiniteAbelianChargeSectors
open PhysicalChainSource StandardSU5Inclusion

variable {H : Type*} [CommGroup H]
  (R : ActualUnitaryGroupRepresentation (ChargedAmbientRealization.AmbientGroup H))
  (S : ActualUnitaryGroupRepresentation (StandardSMCharacterTarget.CombinedGroup H))
  (B : SymmetricMass S.rho) (F : FiniteChargeProfiles.Family (ChargeLabel H))
  (s : ChargeLabel H →₀ ℤ)

structure Certificate where
  model : StandardChain.Model inclusion R.rho
  fieldEquiv : R.V ≃ₗᵢ[ℂ] S.V
  action_compatible : ∀ g v,
    fieldEquiv (R.rho (ChargedAmbientRealization.physicalInclusion (-2) 3 g) v) =
      S.rho g (fieldEquiv v)
  mass_compatible : ∀ x y, model.mass.form x y = B.form (fieldEquiv x) (fieldEquiv y)
  radicalEquiv : Representation.Equiv
    (model.mass.radical.toRepresentation.comp SU5TorusCompatibility.cover) B.radical.toRepresentation
  radicalEquiv_apply : ∀ x, (radicalEquiv x).val = fieldEquiv x.val
  spectrum_compatible : model.lightSpectrum = ProfileZeroModeSupport.spectrum S B
  profile_eq : model.profile = F
  singlets_eq : model.singlets = s

def ofEq (h : physicalFields R = S)
    (ht : ProfileZeroModeSupport.HasTarget S B F.profiles s) : Certificate R S B F s :=
  Classical.choice (by
    subst S
    refine ⟨{
      model := PhysicalChainSource.model R B F s ht
      fieldEquiv := LinearIsometryEquiv.refl ℂ _
      action_compatible := fun _ _ => rfl
      mass_compatible := fun _ _ => rfl
      radicalEquiv := PhysicalChainSource.radicalEquiv R B
      radicalEquiv_apply := fun _ => rfl
      spectrum_compatible := PhysicalChainSource.model_spectrum R B F s ht
      profile_eq := rfl
      singlets_eq := rfl }⟩)

variable {R S B F s} (C : Certificate R S B F s)

theorem mass_nonzero_iff : C.model.mass.form ≠ 0 ↔ B.form ≠ 0 := by
  constructor
  · intro hn hz
    apply hn
    ext x y
    rw [C.mass_compatible, hz]
    rfl
  · intro hn hz
    apply hn
    ext x y
    obtain ⟨a, rfl⟩ := C.fieldEquiv.surjective x
    obtain ⟨b, rfl⟩ := C.fieldEquiv.surjective y
    rw [← C.mass_compatible, hz]
    rfl

theorem radical_finrank : Module.finrank ℂ C.model.mass.radical.toSubmodule =
    Module.finrank ℂ B.radical.toSubmodule := C.radicalEquiv.toLinearEquiv.finrank_eq

end

end GUT.SU6.CanonicalChainTransport
