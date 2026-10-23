import Math.RepresentationTheory.Weights.RationalCircleTests
import Math.LieGroups.SpecialUnitary.ColorPlaneCircles

/-! Rational-coordinate circle tests exhaust the compact SU2/SU3 factors. -/
namespace Math.RationalCompactTests
set_option autoImplicit false
noncomputable section
open Representation

def weak (b : Bool) : TauCeti.SU2 := if b then
  TwoCircleGeneration.mix * TauCeti.SU2.torusHom RationalCircleTests.sample * TwoCircleGeneration.mix⁻¹
  else TauCeti.SU2.torusHom RationalCircleTests.sample

theorem weak_exhaustive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ TauCeti.SU2 V)
    (hi : IntegralTorusTests.Integral rho TauCeti.SU2.torusHom) :
    FiniteInvariantKernel.Exhaustive rho weak := by
  intro f hf
  apply TwoCircleGeneration.invariant rho f
  · exact RationalCircleTests.invariant rho _ hi f (hf false)
  · exact RationalCircleTests.conjugate_invariant rho _ hi TwoCircleGeneration.mix f (hf true)

def color (i : Fin 3 × Bool) : ColorPlaneCircles.SU3 :=
  ColorPlaneCircles.embedding i.1 (weak i.2)

open ColorPlaneCircles

theorem color_exhaustive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) (hi : IntegralTorusTests.Integral rho torus) :
    FiniteInvariantKernel.Exhaustive rho color := by
  intro f hf
  apply invariant rho f
  intro i
  apply TwoCircleGeneration.invariant (rho.comp (embedding i)) f
  · have hs : ∀ x, f (rho (frame i * torus RationalCircleTests.sample * (frame i)⁻¹) x) = f x := by
      intro x
      have he := hf (i,false) x
      change f (rho (embedding i (TauCeti.SU2.torusHom RationalCircleTests.sample)) x) = f x at he
      rw [embedding_conjugate i] at he
      exact he
    have ht := RationalCircleTests.conjugate_invariant rho torus hi (frame i) f hs
    intro z x
    change f (rho (embedding i (TauCeti.SU2.torusHom z)) x) = f x
    rw [embedding_conjugate i]
    exact ht z x
  · have hs : ∀ x, f (rho ((frame i * embedding 0 TwoCircleGeneration.mix) *
        torus RationalCircleTests.sample * (frame i * embedding 0 TwoCircleGeneration.mix)⁻¹) x) = f x := by
      intro x
      simpa only [color,weak,↓reduceIte,embedding_mix] using hf (i,true) x
    have ht := RationalCircleTests.conjugate_invariant rho torus hi
      (frame i * embedding 0 TwoCircleGeneration.mix) f hs
    intro z x
    simpa only [MonoidHom.comp_apply,embedding_mix] using ht z x


end
end Math.RationalCompactTests
