import Math.RepresentationTheory.Relations.LocalCoinvariantHom
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionDegree
import Mathlib.Algebra.Group.Prod

/-! Polynomial spurions realize coefficients invariant under an arbitrary local
group and the actual finite residual stabilizer. Only the residual group is
averaged. The local quotient is constructed from the given product action. -/
namespace Math.LocalSpurionEvaluation
set_option autoImplicit false
noncomputable section
open Representation PolynomialCovariantEvaluation

variable {L H U I : Type*} [Group L] [Group H]
  [AddCommGroup U] [Module ℂ U] (r : Representation ℂ (L × H) U)

abbrev localAction := r.comp (MonoidHom.inl L H)
abbrev residualAction := r.comp (MonoidHom.inr L H)

theorem commute (g : L) (h : H) (u : U) :
    localAction r g (residualAction r h u) =
      residualAction r h (localAction r g u) := by
  change r (g, 1) (r (1, h) u) = r (1, h) (r (g, 1) u)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

abbrev relations := LocalCoinvariantHom.relations (localAction r)
abbrev Quotient := U ⧸ relations r
abbrev quotientAction := LocalCoinvariantHom.quotient
  (localAction r) (residualAction r) (commute r)

variable [Fintype H] [Fintype I] (a : Representation ℂ H (I → ℂ)) (s : I → ℂ)

/-- Coefficients on the original source, with both invariance conditions. -/
abbrev Coefficients := LocalCoinvariantHom.invariantHom (localAction r)
  ((residualAction r).comp (stabilizer a s).subtype)
  (trivial ℂ (stabilizer a s) ℂ)

def coefficientEquiv : Coefficients r a s ≃ₗ[ℂ]
    IntertwiningMap ((quotientAction r).comp (stabilizer a s).subtype)
      (trivial ℂ (stabilizer a s) ℂ) :=
  LocalCoinvariantHom.equiv (localAction r)
    ((residualAction r).comp (stabilizer a s).subtype)
    (trivial ℂ (stabilizer a s) ℂ) (fun g h => commute r g h.val)

omit [Fintype H] [Fintype I] in
@[simp] theorem coefficientEquiv_mk (f : Coefficients r a s) (u : U) :
    coefficientEquiv r a s f ((relations r).mkQ u) = f.val u := rfl

omit [Fintype H] [Fintype I] in
@[simp] theorem coefficientEquiv_symm_apply
    (f : IntertwiningMap ((quotientAction r).comp (stabilizer a s).subtype)
      (trivial ℂ (stabilizer a s) ℂ)) (u : U) :
    ((coefficientEquiv r a s).symm f).val u = f ((relations r).mkQ u) := rfl

variable [FiniteDimensional ℂ U]

/-- Coordinates are chosen on the dual of the actual local quotient. -/
def coordinates := (Module.finBasis ℂ (Module.Dual ℂ (Quotient r))).equivFun
abbrev dualAction := coordinateAction (coordinates r) (quotientAction r).dual

def evaluation (d : ℕ) : boundedCovariants a (dualAction r) d →ₗ[ℂ]
    Coefficients r a s :=
  (coefficientEquiv r a s).symm.toLinearMap.comp
    (boundedCoefficientEvaluation a (quotientAction r) (coordinates r) s d)

omit [Fintype H] [Fintype I] in
@[simp] theorem evaluation_apply (d : ℕ)
    (p : boundedCovariants a (dualAction r) d) (u : U) :
    (evaluation r a s d p).val u =
      (coordinates r).symm (evaluate s p.val.val) ((relations r).mkQ u) := rfl

theorem evaluation_surjective :
    Function.Surjective (evaluation r a s (orbitSize a s - 1)) :=
  (coefficientEquiv r a s).symm.surjective.comp
    (boundedCoefficientEvaluation_surjective a (quotientAction r) (coordinates r) s)

theorem card_evaluation_surjective :
    Function.Surjective (evaluation r a s (Fintype.card H - 1)) :=
  (coefficientEquiv r a s).symm.surjective.comp
    (card_boundedCoefficientEvaluation_surjective a (quotientAction r) (coordinates r) s)

theorem nonzero_iff : (∃ f : Coefficients r a s, f ≠ 0) ↔
    ∃ p, evaluation r a s (orbitSize a s - 1) p ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp⟩ := evaluation_surjective r a s f
    exact ⟨p, hp ▸ hf⟩
  · rintro ⟨p, hp⟩
    exact ⟨_, hp⟩

theorem forbidden_iff : (∀ f : Coefficients r a s, f = 0) ↔
    ∀ p, evaluation r a s (orbitSize a s - 1) p = 0 := by
  constructor
  · intro hf p; exact hf _
  · intro hp f
    obtain ⟨p, rfl⟩ := evaluation_surjective r a s f
    exact hp p

/-- At the zero value, degree zero still attains every allowed coefficient. -/
theorem zero_evaluation_surjective : Function.Surjective (evaluation r a 0 0) := by
  have he : orbitSize a (0 : I → ℂ) - 1 = 0 := by rw [orbitSize_zero]
  exact he ▸ evaluation_surjective r a (0 : I → ℂ)

end
end Math.LocalSpurionEvaluation
