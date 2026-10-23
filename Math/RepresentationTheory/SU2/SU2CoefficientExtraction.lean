import Math.RepresentationTheory.SU2.SU2WeightExtraction
import Math.LinearAlgebra.Selection.SelectionCriteria
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Instances.Matrix

/-! A1 and A1 × A1 weight extraction for invariant coefficient spaces. -/
namespace Math.SU2CoefficientExtraction
set_option autoImplicit false
noncomputable section
open Representation MeasureTheory TauCeti
open scoped BigOperators

local instance : SecondCountableTopology SU2 := inferInstanceAs
  (SecondCountableTopology {g : Fin 2 → Fin 2 → ℂ // g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ})

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem allowed_iff_finrank_ne_zero : SelectionCriteria.Allowed V ↔
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  simp only [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero,
    Module.finrank_pos_iff_exists_ne_zero, SelectionCriteria.Allowed]

theorem finrank (rho : Representation ℂ SU2 V)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho) (c : ℕ →₀ ℂ)
    (ht : ∀ z, rho.character (SU2.torusHom z) =
      c.sum (fun k a => a * SU2WeightExtraction.pairWeight k z)) :
    (Module.finrank ℂ (IntertwiningMap rho (trivial ℂ SU2 ℂ)) : ℂ) = c 0 - c 2 := by
  have h := CompactHomDimension.integral_character_mul_eq_finrank
    rho (trivial ℂ SU2 ℂ) hr continuous_snd
  have he := SU2WeightExtraction.integral_of_weight_expansion rho.character c
    (fun u g => Representation.char_conj rho g u) ht
  have hi : (∫ g, rho.character g ∂haarProb SU2) =
      (Module.finrank ℂ (IntertwiningMap rho (trivial ℂ SU2 ℂ)) : ℂ) := by
    simpa [integral_inv_eq_self] using h
  exact hi.symm.trans he

theorem haarProb_prod : haarProb (SU2 × SU2) = (haarProb SU2).prod (haarProb SU2) :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem pair_finrank (rho : Representation ℂ (SU2 × SU2) V)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous rho) (c : ℕ × ℕ →₀ ℂ)
    (ht : ∀ z w, rho.character (SU2.torusHom z, SU2.torusHom w) =
      c.sum (fun k a => a * SU2WeightExtraction.pairWeight k.1 z *
        SU2WeightExtraction.pairWeight k.2 w)) :
    (Module.finrank ℂ (IntertwiningMap rho (trivial ℂ (SU2 × SU2) ℂ)) : ℂ) =
      c (0,0) - c (0,2) - c (2,0) + c (2,2) := by
  have h := CompactHomDimension.integral_character_mul_eq_finrank
    rho (trivial ℂ (SU2 × SU2) ℂ) hr continuous_snd
  have hc : Continuous rho.character :=
    (ContRepresentation.character (CompactHomDimension.asContinuous rho)
      (CompactHomDimension.continuous_asContinuous rho hr)).continuous
  have hi : Integrable rho.character ((haarProb SU2).prod (haarProb SU2)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : (∫ g, rho.character g ∂haarProb (SU2 × SU2)) =
      (Module.finrank ℂ (IntertwiningMap rho (trivial ℂ (SU2 × SU2) ℂ)) : ℂ) := by
    simpa [integral_inv_eq_self] using h
  rw [haarProb_prod, integral_prod _ hi] at hd
  have he := SU2WeightExtraction.integral_pair_of_weight_expansion
    (fun g h => rho.character (g,h)) c
    (fun u g h => by simpa using Representation.char_conj rho (g,h) (u,1))
    (fun u g h => by simpa using Representation.char_conj rho (g,h) (1,u)) ht
  exact hd.symm.trans he

end
end Math.SU2CoefficientExtraction
