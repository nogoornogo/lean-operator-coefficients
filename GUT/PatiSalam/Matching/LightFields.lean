import GUT.PatiSalam.Matching.TypedVertex
import Math.RepresentationTheory.Constructions.MixedSingleBosonEvaluation

open Physics

/-! Selected LEFT components: uR,dR,uL,dL and the anti-neutrino Weyl line.
The neutrino chart has nuL coordinate one; it is not canonically normalized. -/
namespace GUT.PatiSalam.LightFields
noncomputable section
open Math GUT Representation SMEpsilonTensor StandardSMContragredient
open scoped TensorProduct
abbrev Quark := Color ⊗[ℂ] WeylSpinor.Space
abbrev Light := (Fin 4 → Quark) × WeylSpinor.Space
abbrev Full := ∀ s, DeltaLOneSignedFields.Field (F := fun _ => ℂ) s

def withFlavor : Quark →ₗ[ℂ] Quark ⊗[ℂ] ℂ :=
  (TensorProduct.mk ℂ Quark ℂ).flip 1

def quarkWeak (w : Weak) : Quark →ₗ[ℂ] ((Color ⊗[ℂ] Weak) ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] ℂ :=
  ((TensorProduct.mk ℂ _ ℂ).flip 1).comp
    (TensorProduct.map ((TensorProduct.mk ℂ Color Weak).flip w) LinearMap.id)

def neutrino : WeylSpinor.Space →ₗ[ℂ] (Module.Dual ℂ Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] ℂ :=
  ((TensorProduct.mk ℂ _ ℂ).flip 1).comp
    (TensorProduct.mk ℂ (Module.Dual ℂ Weak) WeylSpinor.Space
      (weakDualLinearEquiv (weakBasis 1)))

def quarkProjection (i : Fin 4) : Light →ₗ[ℂ] Quark :=
  (LinearMap.proj i).comp (LinearMap.fst ℂ (Fin 4 → Quark) WeylSpinor.Space)

def injection : Light →ₗ[ℂ] Full := LinearMap.pi (fun s => match s with
    | 0 => (quarkWeak (weakBasis 0)).comp (quarkProjection 2) +
        (quarkWeak (weakBasis 1)).comp (quarkProjection 3)
    | 1 => withFlavor.comp (quarkProjection 0)
    | 2 => withFlavor.comp (quarkProjection 1)
    | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
    | 8 => neutrino.comp (LinearMap.snd ℂ (Fin 4 → Quark) WeylSpinor.Space)
    | 9 => 0)

def rrProbe : Fin 4 → Light := ![
  (Pi.single 0 (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0),0),
  (Pi.single 1 (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1),0),
  (Pi.single 1 (colorBasis 2 ⊗ₜ[ℂ] weakBasis 0),0),
  (0,weakBasis 1)]
def lrProbe : Fin 4 → Light := ![
  (Pi.single 2 (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0),0),
  (Pi.single 3 (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1),0),
  (Pi.single 1 (colorBasis 2 ⊗ₜ[ℂ] weakBasis 0),0),
  (0,weakBasis 1)]

theorem rr_probe_fields : injection ∘ rrProbe =
    fun i => Pi.single (BnvSevenPatternDescent.pattern 0 i) (TypedVertex.rrProbe i) := by
  funext i s
  fin_cases i <;> fin_cases s <;>
    simp [injection, quarkProjection, rrProbe, TypedVertex.rrProbe, TypedVertex.rrInputs,
      BnvSevenPatternDescent.pattern, withFlavor, quarkWeak, neutrino]
    <;> symm
    <;> first | exact Pi.single_eq_same _ _ | exact Pi.single_eq_of_ne (by decide) _

theorem lr_probe_fields : injection ∘ lrProbe =
    fun i => Pi.single (BnvSevenPatternDescent.pattern 1 i) (TypedVertex.lrProbe i) := by
  funext i s
  fin_cases i <;> fin_cases s <;>
    simp [injection, quarkProjection, lrProbe, TypedVertex.lrProbe, TypedVertex.lrInputs,
      BnvSevenPatternDescent.pattern, withFlavor, quarkWeak, neutrino,
      TensorProduct.map_tmul]
    <;> symm
    <;> first | exact Pi.single_eq_same _ _ | exact Pi.single_eq_of_ne (by decide) _

def leftCoefficient (p : Fin 4) (w : ℂ) := MixedSingleBosonEvaluation.pull
  (TypedVertex.assembled p).toLinearMap
  (Pi.single (1 : BnvMixedInput.ScalarSpecies) (w • TypedVertex.neutralHiggs)) injection

theorem rr_value (w : ℂ) : leftCoefficient 0 w rrProbe = -(w/2) := by
  rw [leftCoefficient, MixedSingleBosonEvaluation.pull_apply, rr_probe_fields]
  change TypedVertex.assembled 0 (MixedWeightSupport.pure
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 i) (TypedVertex.rrProbe i))
    (fun _ : Fin 1 => Pi.single 1 (w • TypedVertex.neutralHiggs))) = _
  have hs := (MixedSingleBosonDescent.orderedEquiv 4
    (TypedVertex.assembled 0).toLinearMap
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 i) (TypedVertex.rrProbe i))).map_smul w
    (Pi.single 1 TypedVertex.neutralHiggs)
  rw [Pi.single_smul]
  change TypedVertex.assembled 0 (MixedWeightSupport.pure
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 i) (TypedVertex.rrProbe i))
    (fun _ : Fin 1 => w • Pi.single 1 TypedVertex.neutralHiggs)) =
      w • TypedVertex.assembled 0 TypedVertex.rrExteriorProbe at hs
  rw [hs, TypedVertex.rr_probe_value]
  simp only [smul_eq_mul]
  ring

theorem lr_value (w : ℂ) : leftCoefficient 1 w lrProbe = -w := by
  rw [leftCoefficient, MixedSingleBosonEvaluation.pull_apply, lr_probe_fields]
  have hs := (MixedSingleBosonDescent.orderedEquiv 4
    (TypedVertex.assembled 1).toLinearMap
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 i) (TypedVertex.lrProbe i))).map_smul w
    (Pi.single 1 TypedVertex.neutralHiggs)
  change TypedVertex.assembled 1 (MixedWeightSupport.pure
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 i) (TypedVertex.lrProbe i))
    (fun _ : Fin 1 => Pi.single 1 (w • TypedVertex.neutralHiggs))) = _
  rw [Pi.single_smul]
  change TypedVertex.assembled 1 (MixedWeightSupport.pure
    (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 i) (TypedVertex.lrProbe i))
    (fun _ : Fin 1 => w • Pi.single 1 TypedVertex.neutralHiggs)) =
      w • TypedVertex.assembled 1 TypedVertex.lrExteriorProbe at hs
  rw [hs, TypedVertex.lr_probe_value]
  simp

theorem left_zero (p : Fin 4) : leftCoefficient p 0 = 0 := by
  unfold leftCoefficient
  simp only [zero_smul, Pi.single_zero]
  exact MixedSingleBosonEvaluation.pull_zero _ _

theorem lr_at_rr (w : ℂ) : leftCoefficient 1 w rrProbe = 0 := by
  rw [leftCoefficient, MixedSingleBosonEvaluation.pull_apply, rr_probe_fields]
  exact (TypedVertex.familyCoefficient 1).property
    (BnvSevenPatternDescent.pattern 0) 1 TypedVertex.rrProbe (w • TypedVertex.neutralHiggs)
    (Or.inl (by decide +kernel))

theorem rr_at_lr (w : ℂ) : leftCoefficient 0 w lrProbe = 0 := by
  rw [leftCoefficient, MixedSingleBosonEvaluation.pull_apply, lr_probe_fields]
  exact (TypedVertex.familyCoefficient 0).property
    (BnvSevenPatternDescent.pattern 1) 1 TypedVertex.lrProbe (w • TypedVertex.neutralHiggs)
    (Or.inl (by decide +kernel))

def combined (a b w : ℂ) := a • leftCoefficient 1 w + b • leftCoefficient 0 w

theorem combined_rr (a b w : ℂ) : combined a b w rrProbe = -(b*w/2) := by
  simp [combined, lr_at_rr, rr_value, smul_eq_mul]
  ring

theorem combined_lr (a b w : ℂ) : combined a b w lrProbe = -(a*w) := by
  simp [combined, rr_at_lr, lr_value, smul_eq_mul]

theorem combined_nonzero_iff (a b w : ℂ) :
    combined a b w ≠ 0 ↔ w ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0) := by
  constructor
  · intro hn
    constructor
    · intro hw
      subst w
      exact hn (by simp [combined, left_zero])
    · by_contra h
      push Not at h
      rcases h with ⟨rfl,rfl⟩
      exact hn (by simp [combined])
  · rintro ⟨hw,ha|hb⟩ hz
    · have h := DFunLike.congr_fun hz lrProbe
      rw [combined_lr] at h
      have : a*w ≠ 0 := mul_ne_zero ha hw
      exact this (by simpa using h)
    · have h := DFunLike.congr_fun hz rrProbe
      rw [combined_rr] at h
      have : b*w ≠ 0 := mul_ne_zero hb hw
      exact this (by simpa using h)

end
end GUT.PatiSalam.LightFields
