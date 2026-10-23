import GUT.SU6.SelectionRules.Models.CanonicalChainTransport
import GUT.SU6.SelectionRules.Models.ContinuousProfileModel

open Physics

/-! The existing positive canonical SU(6) models inhabit the common chain
interface. Their proved hypercharge rigidity is used, not replaced by a new
standard-embedding premise. The field action, mass and full spectrum agree. -/

set_option autoImplicit false

namespace GUT.SU6.CanonicalChainModel

noncomputable section

open UnitaryVirtualRealization InvariantWeylMass FiniteAbelianChargeSectors
open StandardBlockGaugeCancellation PhysicalMassSpectrumBridge
open PhysicalChainSource StandardSU5Inclusion

variable {H : Type*} [CommGroup H]

def ambientFields (matter : OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation (ChargedAmbientRealization.AmbientGroup H) :=
  ChargedAmbientRealization.positive (PhysicalChargeResolvedBridge.ordinaryChargedSource matter)

variable (M : ContinuousProfileModel.Model H)

theorem fields_eq : physicalFields (ambientFields M.matter) = M.fields := by
  change physicalFields (ambientFields M.matter) =
    ordinaryPositiveRepresentation M.geometry.hyperchargePair.1 M.geometry.hyperchargePair.2 M.matter
  rw [M.hyperchargePair_eq_standard]
  exact ChargedAmbientRealization.restrict_positive (-2) 3 _

/-- Keep the bundled field action explicit during dependent transports. -/
def sourceMass : SymmetricMass M.fields.rho := M.mass

def conversion : CanonicalChainTransport.Certificate (ambientFields M.matter) M.fields
    (sourceMass M) M.profile M.singlets :=
  CanonicalChainTransport.ofEq _ _ _ _ _ (fields_eq M) M.lightTarget

/-- This is an actual isometry of the old and lifted canonical fields. -/
def fieldEquiv : (ambientFields M.matter).V ≃ₗᵢ[ℂ] M.fields.V := (conversion M).fieldEquiv

def model : StandardChain.Model inclusion (ambientFields M.matter).rho :=
  (conversion M).model

theorem model_profile : (model M).profile = M.profile := (conversion M).profile_eq

theorem model_singlets : (model M).singlets = M.singlets := (conversion M).singlets_eq

/-- The old interface imposes no topology on H. Joint continuity of the
full product action is therefore explicit, rather than silently inferred. -/
def continuousModel [TopologicalSpace H] [IsTopologicalGroup H]
    (hc : Continuous (fun p : (ChargedAmbientRealization.AmbientGroup H) ×
      (ambientFields M.matter).V => (ambientFields M.matter).rho p.1 p.2)) :
    StandardChain.ContinuousModel inclusion (ambientFields M.matter).rho where
  toModel := model M
  inclusion_injective := inclusion_injective
  inclusion_continuous := inclusion_continuous
  action_continuous := hc

theorem action_compatible (g : StandardSMCharacterTarget.CombinedGroup H)
    (v : (ambientFields M.matter).V) :
    fieldEquiv M ((ambientFields M.matter).rho
      (ChargedAmbientRealization.physicalInclusion (-2) 3 g) v) =
      M.fields.rho g (fieldEquiv M v) := (conversion M).action_compatible g v

theorem mass_compatible (x y : (ambientFields M.matter).V) :
    (model M).mass.form x y = M.mass.form (fieldEquiv M x) (fieldEquiv M y) :=
  (conversion M).mass_compatible x y

theorem mass_nonzero_iff : (model M).mass.form ≠ 0 ↔ M.mass.form ≠ 0 :=
  CanonicalChainTransport.mass_nonzero_iff (conversion M)

def radicalEquiv : Representation.Equiv
    ((model M).mass.radical.toRepresentation.comp SU5TorusCompatibility.cover)
    M.mass.radical.toRepresentation :=
  (conversion M).radicalEquiv

theorem radicalEquiv_apply (x : (model M).mass.radical.toSubmodule) :
    (radicalEquiv M x).val = fieldEquiv M x.val := (conversion M).radicalEquiv_apply x

theorem radical_character (g : StandardSMCharacterTarget.CombinedGroup H) :
    (model M).mass.radical.toRepresentation.character (SU5TorusCompatibility.cover g) =
      M.mass.radical.toRepresentation.character g :=
  congrFun (Representation.char_iso (radicalEquiv M)) g

theorem radical_finrank : Module.finrank ℂ (model M).mass.radical.toSubmodule =
    Module.finrank ℂ M.mass.radical.toSubmodule := CanonicalChainTransport.radical_finrank (conversion M)

theorem spectrum_compatible : (model M).lightSpectrum = M.lightSpectrum :=
  (conversion M).spectrum_compatible

theorem selection_rule_obstruction :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum := by
  rw [← spectrum_compatible M]
  exact (model M).selection_rule_obstruction

/-- Evaluation of a legacy scalar family is preserved. No descent of its
scalar representation through the finite torus kernel is asserted. -/
theorem scalar_mass_compatible (S : ContinuousProfileModel.ScalarModel H)
    (x y : (ambientFields S.matter).V) :
    (model S.toMassModel).mass.form x y =
      S.sector.bareMass.form (fieldEquiv S.toMassModel x) (fieldEquiv S.toMassModel y) +
        S.sector.family.toFun S.sector.vacuum.value
          (fieldEquiv S.toMassModel x) (fieldEquiv S.toMassModel y) :=
  mass_compatible S.toMassModel x y

end

end GUT.SU6.CanonicalChainModel
