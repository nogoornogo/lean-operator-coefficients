import GUT.SU6.SelectionRules.Models.ColorWeakNormalizerSample
import Math.RepresentationTheory.Constructions.PointwiseGaugeRemoval

open Physics

/-! An SM-preserving inner action: the color probe is an unbroken gauge
element, and its factor cannot change a gauge-invariant coefficient. -/
namespace GUT.SMNormalizingColorSample
set_option autoImplicit false
noncomputable section
open Representation ColorWeakNormalizerSample
abbrev K := StandardSMGaugeTensor.GaugeGroup

def beta : K →* K := (MulAut.conj gaugeProbe).toMonoidHom

theorem normalizes (g : K) : StandardSMGroup.hom (beta g) =
    colorProbe * StandardSMGroup.hom g * colorProbe⁻¹ := by
  change StandardSMGroup.hom (gaugeProbe * g * gaugeProbe⁻¹) = _
  simp only [map_mul, map_inv, probe_in_image]

theorem invariant_color_factor {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ K V)
    (f : IntertwiningMap rho (Representation.trivial ℂ K ℂ)) (v : V) :
    f (rho gaugeProbe v) = f v := by
  simpa only [Representation.trivial_apply] using
    IntertwiningMap.isIntertwining _ _ f gaugeProbe v

end
end GUT.SMNormalizingColorSample
