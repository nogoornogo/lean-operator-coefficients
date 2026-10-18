import GUT.SU6.Yukawa.VacuumImage
import Physics.FieldTheory.Yukawa.YukawaClassification
import Math.LinearAlgebra.SplitEvaluation

open Math

/-! The full actual coupling space, its measured coordinates and a realized section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6CouplingEvaluation
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6FiveCouplings SU6YukawaImage

local instance : AddCommGroup (SymmetricScalarYukawa.Scalar uvRho) := inferInstance

abbrev Couplings := Representation.IntertwiningMap StandardSMUVYukawa.scalar.rho
  (SymmetricScalarYukawa.scalarRho uvRho)

local instance : AddCommGroup Couplings := inferInstance
local instance : FiniteDimensional ℂ Couplings := inferInstance

def ofYukawa := YukawaClassification.toMap StandardSMUVYukawa.scalar.rho uvRho
def toYukawa := YukawaClassification.ofMap StandardSMUVYukawa.scalar.rho uvRho

def probes : LinearMap.BilinForm ℂ UV →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun B := ![B probeQ (probeA 0), B probeQ (probeB 0),
    B (probeA 5) (probeA 5), B (probeA 5) (probeB 5), B (probeB 5) (probeB 5)]
  map_add' B C := by funext i; fin_cases i <;> rfl
  map_smul' c B := by funext i; fin_cases i <;> rfl

variable (H : Type*) [CommGroup H]

def evaluation : Couplings →ₗ[ℂ] LinearMap.BilinForm ℂ UV where
  toFun f := (f (StandardSMUVYukawa.vacuum H)).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : Couplings →ₗ[ℂ] (Fin 5 → ℂ) := probes.comp (evaluation H)

theorem coordinates_apply (f : Couplings) : coordinates H f = probes (evaluation H f) := rfl

theorem evaluation_ofYukawa
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    evaluation H (ofYukawa Y) = Y.toLinearMap (StandardSMUVYukawa.vacuum H) := rfl

theorem evaluation_toYukawa (f : Couplings) :
    (toYukawa f).toLinearMap (StandardSMUVYukawa.vacuum H) = evaluation H f := rfl

theorem probes_eq (B : LinearMap.BilinForm ℂ UV) (c : Fin 5 → ℂ)
    (hp : B probeQ (probeA 0) = c 0 ∧ B probeQ (probeB 0) = c 1 ∧
      B (probeA 5) (probeA 5) = c 2 ∧ B (probeA 5) (probeB 5) = c 3 ∧
      B (probeB 5) (probeB 5) = c 4) : probes B = c := by
  funext i
  fin_cases i
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2

theorem probes_mass (c : Fin 5 → ℂ) :
    probes (mass H (c 0) (c 1) (c 2) (c 3) (c 4)).form = c :=
  probes_eq _ c (probe_values H _ _ _ _ _)

theorem coordinates_coupling (c : Fin 5 → ℂ) :
    coordinates H (ofYukawa (coupling (c 0) (c 1) (c 2) (c 3) (c 4))) = c :=
  (coordinates_apply H _).trans ((congrArg probes (evaluation_ofYukawa H _)).trans
    ((congrArg probes (coupling_evaluation H _ _ _ _ _)).trans (probes_mass H c)))

def sectionMap : (Fin 5 → ℂ) →ₗ[ℂ] Couplings :=
  (Pi.basisFun ℂ (Fin 5)).constr ℂ fun i =>
    let c := (Pi.basisFun ℂ (Fin 5)) i
    ofYukawa (coupling (c 0) (c 1) (c 2) (c 3) (c 4))

theorem coordinates_section (c : Fin 5 → ℂ) : coordinates H (sectionMap c) = c := by
  have h : (coordinates H).comp sectionMap = LinearMap.id := by
    apply (Pi.basisFun ℂ (Fin 5)).ext
    intro i
    simp only [LinearMap.comp_apply, sectionMap, Module.Basis.constr_basis,
      coordinates_coupling, LinearMap.id_apply]
  exact LinearMap.congr_fun h c

theorem evaluation_eq_iff (f g : Couplings) :
    evaluation H f = evaluation H g ↔ coordinates H f = coordinates H g := by
  constructor
  · exact congrArg probes
  · intro h
    apply evaluation_eq_of_probes H (toYukawa f) (toYukawa g)
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4⟩

theorem kernel_eq : (coordinates H).ker = (evaluation H).ker := by
  ext f
  simp only [LinearMap.mem_ker]
  simpa only [map_zero] using (evaluation_eq_iff H f 0).symm

def split : Couplings ≃ₗ[ℂ] (evaluation H).ker × (Fin 5 → ℂ) :=
  SplitEvaluation.equivWithKernel (coordinates H) sectionMap (coordinates_section H)
    (evaluation H).ker (kernel_eq H)

theorem coordinates_surjective : Function.Surjective (coordinates H) :=
  SplitEvaluation.surjective (coordinates H) sectionMap (coordinates_section H)

def quotientEquiv : (Couplings ⧸ (coordinates H).ker) ≃ₗ[ℂ] (Fin 5 → ℂ) :=
  (coordinates H).quotKerEquivOfSurjective (coordinates_surjective H)

theorem quotient_finrank : Module.finrank ℂ (Couplings ⧸ (evaluation H).ker) = 5 := by
  rw [← kernel_eq, (quotientEquiv H).finrank_eq]
  simp

theorem dimension_split : Module.finrank ℂ Couplings =
    Module.finrank ℂ (evaluation H).ker + 5 := by
  rw [(split H).finrank_eq, Module.finrank_prod]
  simp

theorem dimension_twenty_two_iff : Module.finrank ℂ Couplings = 22 ↔
    Module.finrank ℂ (evaluation H).ker = 17 := by
  rw [dimension_split H]
  omega

theorem evaluation_section (c : Fin 5 → ℂ) :
    evaluation H (sectionMap c) = massMap H c := by
  change evaluation H (sectionMap c) = (mass H (c 0) (c 1) (c 2) (c 3) (c 4)).form
  rw [← coupling_evaluation H (c 0) (c 1) (c 2) (c 3) (c 4)]
  rw [← evaluation_ofYukawa]
  apply (evaluation_eq_iff H _ _).mpr
  rw [coordinates_section, coordinates_coupling]

theorem reconstruction (f : Couplings) :
    evaluation H f = massMap H (coordinates H f) := by
  rw [← evaluation_section]
  apply (evaluation_eq_iff H _ _).mpr
  rw [coordinates_section]

theorem unique_decomposition (f : Couplings) :
    ∃! p : (evaluation H).ker × (Fin 5 → ℂ), f = p.1.val + sectionMap p.2 := by
  refine ⟨split H f, ?_, ?_⟩
  · exact ((split H).symm_apply_apply f).symm.trans
      (SplitEvaluation.equivWithKernel_symm_apply (coordinates H) sectionMap
        (coordinates_section H) (evaluation H).ker (kernel_eq H) (split H f))
  · intro p hp
    apply (split H).symm.injective
    change (SplitEvaluation.equivWithKernel (coordinates H) sectionMap
      (coordinates_section H) (evaluation H).ker (kernel_eq H)).symm p = _
    rw [SplitEvaluation.equivWithKernel_symm_apply]
    exact hp.symm.trans ((split H).symm_apply_apply f).symm

end
end GUT.SU6CouplingEvaluation
