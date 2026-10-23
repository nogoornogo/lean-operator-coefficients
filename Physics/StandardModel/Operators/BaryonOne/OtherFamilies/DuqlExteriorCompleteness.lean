import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlOrderedCompleteness
import Math.RepresentationTheory.Exterior.DistinctSpeciesAlternation
import Math.RepresentationTheory.Tensors.FourTensorMultilinear

open Math

/-! Independent one-of-each exterior duql coefficients and residual Hom. -/
namespace Physics.DuqlExteriorCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor DuqlOrderedCompleteness
open scoped TensorProduct
universe u
variable {R : Type*} [Group R] {D U Q L : Type u}
  [AddCommGroup D] [Module ℂ D] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup L] [Module ℂ L]

variable (D U Q L) in
abbrev Carrier : Fin 4 → Type u := ![
  (SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D,
  (SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U,
  (StandardSMGaugeTensor.Quark ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q,
  (SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] L]

instance (i : Fin 4) : AddCommGroup (Carrier D U Q L i) := by
  dsimp [Carrier]
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => nomatch i)))) i
  · exact inferInstanceAs (AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D))
  · exact inferInstanceAs (AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U))
  · exact Module.addCommMonoidToAddCommGroup ℂ
      (M := (StandardSMGaugeTensor.Quark ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q)
  · exact inferInstanceAs (AddCommGroup ((SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] L))
instance (i : Fin 4) : Module ℂ (Carrier D U Q L i) := by
  dsimp [Carrier]
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => nomatch i)))) i
  · exact inferInstanceAs (Module ℂ ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D))
  · exact inferInstanceAs (Module ℂ ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U))
  · exact inferInstanceAs (Module ℂ ((StandardSMGaugeTensor.Quark ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q))
  · exact inferInstanceAs (Module ℂ ((SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] L))

variable (d : Representation ℂ R D) (u : Representation ℂ R U)
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

def species : ∀ i, Representation ℂ ((GaugeGroup × WeylSpinor.Group) × R) (Carrier D U Q L i)
  | 0 => external downSpin d
  | 1 => external upSpin u
  | 2 => external quarkSpin q
  | 3 => external leptonSpin l

/-- Defined by degree support in the full exterior power, not by contractions. -/
abbrev Sector := DistinctSpeciesAlternation.exteriorSector (species d u q l)

def orderedEquiv : Sector d u q l ≃ₗ[ℂ] Coefficient d u q l :=
  (DistinctSpeciesAlternation.exteriorEquiv (species d u q l)).symm.trans
    ((DistinctSpeciesAlternation.invariantEquiv (species d u q l)).symm.trans
      (FourTensorMultilinear.invariantEquiv (species d u q l)))

/-- Complete duql exterior classification for arbitrary residual representations. -/
def homEquiv : Sector d u q l ≃ₗ[ℂ] Residual d u q l :=
  (orderedEquiv d u q l).trans (DuqlOrderedCompleteness.homEquiv d u q l)

theorem exists_nonzero_iff : (∃ f : Sector d u q l, f ≠ 0) ↔
    ∃ k : Residual d u q l, k ≠ 0 := by
  let e := homEquiv d u q l
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨e f, fun h => hf (e.injective (h.trans e.map_zero.symm))⟩
  · rintro ⟨k,hk⟩
    exact ⟨e.symm k, fun h => hk (e.symm.injective (h.trans e.symm.map_zero.symm))⟩

end
end Physics.DuqlExteriorCompleteness
