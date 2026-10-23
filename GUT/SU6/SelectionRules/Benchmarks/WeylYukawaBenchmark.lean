import GUT.SU6.SelectionRules.Models.ContinuousWeylYukawaModel
import GUT.SU6.SelectionRules.Models.ContinuousWeylFullMass

open Physics

/-!
# Nonzero symmetric Yukawa examples

The first tensor is invariant under the full non-Abelian SU(6) action on
6 + 6*. The second realizes the existing post-breaking 15-mode mass by a
neutral scalar, zero bare mass, and VEV one. That compatibility example does
not assert ultraviolet SU(6) invariance of the post-breaking mass.
-/

set_option autoImplicit false

namespace GUT.WeylYukawaBenchmark

noncomputable section

open WeylYukawaMass InvariantWeylMass
open scoped TensorProduct

namespace AmbientPair

abbrev rho := FundamentalRepresentation.rho

def mass : SymmetricMass (rho.prod rho.dual) :=
  ofDirac (Representation.IntertwiningMap.id rho)

def leftVector : FundamentalRepresentation.Std × Module.Dual ℂ FundamentalRepresentation.Std :=
  (Pi.single 0 1, 0)

def rightVector : FundamentalRepresentation.Std × Module.Dual ℂ FundamentalRepresentation.Std :=
  (0, LinearMap.proj 0)

theorem mass_pair : mass.form leftVector rightVector = 1 := by
  simp [mass, ofDirac, DiracWeylConvention.massBilinear_apply, leftVector, rightVector]

def yukawa := EquivariantYukawa.ofMass mass

def tensor := yukawa.tensorIntertwiner

theorem tensor_pair : tensor.toLinearMap ((1 ⊗ₜ[ℂ] leftVector) ⊗ₜ[ℂ] rightVector) = 1 := by
  change ((EquivariantYukawa.ofMass mass).toLinearMap 1) leftVector rightVector = 1
  rw [EquivariantYukawa.ofMass_one, mass_pair]

theorem tensor_nonzero : tensor.toLinearMap ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h ((1 ⊗ₜ[ℂ] leftVector) ⊗ₜ[ℂ] rightVector)
  rw [tensor_pair] at he
  exact one_ne_zero he

/-- The test group is all of SU(6), not just its diagonal torus. -/
theorem invariant (g : ActualRestriction.SU6) (s : ℂ)
    (x y : FundamentalRepresentation.Std × Module.Dual ℂ FundamentalRepresentation.Std) :
    yukawa.toLinearMap s ((rho.prod rho.dual) g x) ((rho.prod rho.dual) g y) =
      yukawa.toLinearMap s x y :=
  yukawa.invariant g s x y

end AmbientPair

namespace FullMass

open ContinuousWeylYukawaModel StandardSMCharacterTarget ConcreteSU6PhysicalTarget

def model (H : Type*) [CommGroup H] : Model H := Model.ofMassAsYukawa (ContinuousWeylFullMass.model H)

variable {H : Type*} [CommGroup H]

theorem toMassModel : (model H).toMassModel = ContinuousWeylFullMass.model H :=
  Model.ofMassAsYukawa_toMassModel (ContinuousWeylFullMass.model H)

theorem bare_mass_zero : (model H).sector.bareMass.form = 0 := rfl

theorem vacuum_one : (model H).sector.vacuum.value = (1 : ℂ) := rfl

set_option maxHeartbeats 800000 in
theorem yukawa_nonzero : (model H).sector.yukawa.toLinearMap ≠ 0 :=
  EquivariantYukawa.ofMass_nonzero (ContinuousWeylFullMass.model H).mass
    (ContinuousWeylFullMass.mass_nonzero (H := H))

theorem radical_finrank : Module.finrank ℂ (model H).sector.mass.radical.toSubmodule = 15 := by
  change Module.finrank ℂ (model H).toMassModel.mass.radical.toSubmodule = 15
  rw [toMassModel]
  exact ContinuousWeylFullMass.radical_finrank

theorem lightSpectrum : PhysicalWeylZeroModeSupport.lightSpectrum (model H).toMassModel.toPhysical =
    exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 := by
  rw [toMassModel]
  exact ContinuousWeylFullMass.lightSpectrum

theorem exists_yukawa_sm_radical (H : Type*) [CommGroup H] :
    ∃ M : Model H, M.generations = 1 ∧ M.sector.bareMass.form = 0 ∧
      M.sector.yukawa.toLinearMap ≠ 0 ∧ Module.finrank ℂ M.sector.mass.radical.toSubmodule = 15 ∧
      PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ⟨model H, rfl, bare_mass_zero, yukawa_nonzero, radical_finrank, lightSpectrum⟩

end FullMass

end

end GUT.WeylYukawaBenchmark
