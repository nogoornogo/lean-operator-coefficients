import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraParity
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorOneGeneration

/-! Actual two-flavor coefficient witness; not a matching certificate for source Eq.(4). -/
namespace Physics.DevMohapatraSixQuark
set_option autoImplicit false
noncomputable section
open Math Representation SixQuarkInvariant SixQuarkSpeciesQuotient
open SixQuarkFlavorCoordinates SixQuarkFlavorResidualHom
open scoped TensorProduct
abbrev F := Fin 2 → ℂ
abbrev H := DevMohapatraParity.H

def residual : Representation ℂ H F := DevMohapatraParity.copies (1,0)
abbrev Sector := SixQuarkFlavorResidualHom.Coefficients (fun _ : Fin 6 => residual)

def project : Quark ⊗[ℂ] F →ₗ[ℂ] Quark :=
  (TensorProduct.rid ℂ Quark).toLinearMap.comp
    (TensorProduct.map LinearMap.id ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0) + (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1)))

@[simp] theorem project_pure (q : Quark) (t : F) : project (q ⊗ₜ[ℂ] t) = (t 0 + t 1) • q := by
  simp [project]

theorem project_natural (a : Quark →ₗ[ℂ] Quark) (v : Quark ⊗[ℂ] F) :
    project (TensorProduct.map a LinearMap.id v) = a (project v) := by
  have he : project.comp (TensorProduct.map a LinearMap.id) = a.comp project := by
    apply TensorProduct.ext'
    intro q t
    simp
  exact LinearMap.congr_fun he v

def phase (g : H) : ℂ := DevMohapatraParity.chi g (1,0)

theorem phase_six (g : H) : phase g ^ 6 = 1 := by
  have h : phase g ^ 2 = 1 := by
    rw [pow_two]
    unfold phase DevMohapatraParity.chi
    change MixedChargeSelection.cyclicCharacter g (1 : ZMod 2) *
      MixedChargeSelection.cyclicCharacter g (1 : ZMod 2) = 1
    rw [← (MixedChargeSelection.cyclicCharacter g).map_add_eq_mul]
    change MixedChargeSelection.cyclicCharacter g (0 : ZMod 2) = 1
    exact (MixedChargeSelection.cyclicCharacter g).map_zero_eq_one
  calc
    _ = (phase g ^ 2) ^ 3 := by ring
    _ = 1 := by rw [h]; norm_num

theorem project_residual (g : H) (v : Quark ⊗[ℂ] F) :
    project (TensorProduct.map LinearMap.id (residual g) v) = phase g • project v := by
  have he : project.comp (TensorProduct.map LinearMap.id (residual g)) =
      phase g • project := by
    apply TensorProduct.ext'
    intro q t
    simp [residual, DevMohapatraParity.copies, phase, smul_smul, mul_add]
  exact LinearMap.congr_fun he v

def liftCoefficient (b : admissible) : Sector := by
  refine ⟨b.val.compLinearMap (fun _ => project), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g v
    change b.val (fun i => project (TensorProduct.map (colorAction g) LinearMap.id (v i))) = _
    simp_rw [project_natural]
    exact b.property.1.1 g _
  · intro g v
    change b.val (fun i => project (TensorProduct.map (spinAction g) LinearMap.id (v i))) = _
    simp_rw [project_natural]
    exact b.property.1.2 g _
  · intro g v
    change b.val (fun i => project (TensorProduct.map LinearMap.id (residual g) (v i))) = _
    simp_rw [project_residual]
    rw [b.val.map_smul_univ]
    simp [phase_six]
  · intro p hp v
    exact b.property.2 p hp (fun i => project (v i))

/-- Up slots 0,2 use flavor 0; down slots 1,4 use 0 and slots 3,5 use 1. -/
def labels : Fin 6 → Fin 2 := ![0,0,0,1,0,1]

theorem lift_selected (b : admissible) (q : Fin 6 → Quark) :
    (liftCoefficient b).val (fun i => q i ⊗ₜ[ℂ] Pi.single (labels i) 1) = b.val q := by
  change b.val (fun i => project (q i ⊗ₜ[ℂ] Pi.single (labels i) 1)) = b.val q
  congr 1
  funext i
  rw [project_pure]
  fin_cases i <;> simp [labels]

theorem selected_nonzero : ∃ f : Sector, ∃ q : Fin 6 → Quark,
    f.val (fun i => q i ⊗ₜ[ℂ] Pi.single (labels i) 1) ≠ 0 := by
  let b := coefficientProbeEquiv.symm (fun _ => (1 : ℂ))
  have hb : b ≠ 0 := by
    intro h
    have he := congrArg coefficientProbeEquiv h
    simpa [b, coefficientProbeEquiv] using congrFun he 0
  have hv : ∃ q, b.val q ≠ 0 := by
    by_contra hn
    apply hb
    apply Subtype.ext
    apply MultilinearMap.ext
    intro q
    simpa using (not_exists.mp hn q)
  obtain ⟨q,hq⟩ := hv
  exact ⟨liftCoefficient b, q, by rwa [lift_selected]⟩

theorem allowed : SelectionCriteria.Allowed Sector := by
  obtain ⟨f,q,h⟩ := selected_nonzero
  exact ⟨f, fun hz => h (by rw [hz]; rfl)⟩
end
end Physics.DevMohapatraSixQuark

namespace Physics.DevMohapatraSixQuark
set_option autoImplicit false
noncomputable section
open Math MixedSelectionRequests
inductive Target where
  | bOne | sixQuark | llhh
  deriving DecidableEq

def domain : Target → Type
  | .bOne => ∀ n m : ℕ, ComposableBLSupport.Input
      (DevMohapatraParity.flavor (F := fun _ => ℂ))
      (DevMohapatraParity.scalarFlavor (S := fun _ => ℂ))
      (fun q => q.1.natAbs = 3) n m
  | .sixQuark => Sector
  | .llhh => DevMohapatraParity.LLHH

instance (t : Target) : Zero (domain t) := by
  cases t <;> unfold domain <;> infer_instance

def request : Request Target := ⟨{t | t = .bOne}, {t | t = .sixQuark ∨ t = .llhh}⟩

theorem satisfies : Satisfies domain request := by
  constructor
  · intro t ht; change t = .bOne at ht; subst t
    intro f; funext n m
    exact DevMohapatraParity.all_bOne_forbidden n m (f n m)
  · intro t ht
    rcases ht with rfl | rfl
    · exact allowed
    · exact DevMohapatraParity.llhh_allowed
end
end Physics.DevMohapatraSixQuark
