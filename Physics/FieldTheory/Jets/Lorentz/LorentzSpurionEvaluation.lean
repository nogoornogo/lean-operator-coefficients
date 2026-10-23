import Math.RepresentationTheory.Jets.JetSpurionEvaluation
import Physics.FieldTheory.Jets.Lorentz.LorentzDirections

/-! Constant finite-group spurions on four-dimensional massless scalar EOM/IBP
coefficients. Lorentz invariance uses the actual Pauli direction action. -/
namespace Physics.LorentzSpurionEvaluation
set_option autoImplicit false
noncomputable section
open Math Math.JetSpurionEvaluation Math.PolynomialCovariantEvaluation

variable {H S T : Type*} [Group H] [Fintype H] [Finite S] [Fintype T]
  (ρ : Representation ℂ H (JetLinear.Field S)) (n d : ℕ)
  (a : Representation ℂ H (T → ℂ)) (s : T → ℂ)

abbrev Source := ScalarSource (S := S) LorentzDirections.wave n d
def action := scalarAction LorentzDirections.direction LorentzDirections.wave ρ
  LorentzDirections.wave_invariant n d
def sourceEquiv := scalarSourceEquiv LorentzDirections.direction LorentzDirections.wave ρ
  LorentzDirections.wave_invariant n d
abbrev Coefficients := ScalarCoefficients LorentzDirections.direction LorentzDirections.wave ρ
  LorentzDirections.wave_invariant n d a s
def coefficientEquiv := scalarCoefficientEquiv LorentzDirections.direction LorentzDirections.wave ρ
  LorentzDirections.wave_invariant n d a s
def evaluation (b : ℕ) := scalarEvaluation LorentzDirections.direction LorentzDirections.wave ρ
  LorentzDirections.wave_invariant n d a s b

theorem surjective : Function.Surjective (evaluation ρ n d a s (orbitSize a s - 1)) :=
  scalar_surjective LorentzDirections.direction LorentzDirections.wave ρ
    LorentzDirections.wave_invariant n d a s

theorem card_surjective : Function.Surjective (evaluation ρ n d a s (Fintype.card H - 1)) :=
  scalar_card_surjective LorentzDirections.direction LorentzDirections.wave ρ
    LorentzDirections.wave_invariant n d a s

theorem nonzero_iff : (∃ f : Coefficients ρ n d a s, f ≠ 0) ↔
    ∃ p, evaluation ρ n d a s (orbitSize a s - 1) p ≠ 0 :=
  scalar_nonzero_iff LorentzDirections.direction LorentzDirections.wave ρ
    LorentzDirections.wave_invariant n d a s

omit [Fintype H] [Finite S] [Fintype T] in
theorem pullback_injective : Function.Injective
    (fun f : Coefficients ρ n d a s =>
      f.val.toLinearMap.comp (JetEquation.combinedProjection LorentzDirections.wave n d)) :=
  scalar_pullback_injective LorentzDirections.direction LorentzDirections.wave ρ
    LorentzDirections.wave_invariant n d a s

end
end Physics.LorentzSpurionEvaluation
