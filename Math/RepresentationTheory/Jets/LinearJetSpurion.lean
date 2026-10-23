import Math.RepresentationTheory.Jets.LinearJetIBP
import Math.RepresentationTheory.Spurions.LocalSpurionEvaluation

/-! The bounded finite-group evaluation interface survives linear odd/even EOM
and actual IBP, including intrinsic local component actions. -/
namespace Math.LinearJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections PolynomialCovariantEvaluation

variable {F B I EF EB L H T : Type*} [AddCommGroup EF] [Module ℂ EF]
  [AddCommGroup EB] [Module ℂ EB] [Group L] [Group H]
  [Finite F] [Finite B] [Fintype I] [Fintype H] [Fintype T]
  (eF : EF →ₗ[ℂ] Jet F I) (eB : EB →ₗ[ℂ] Jet B I)
  (τF : Representation ℂ (L × H) EF) (τB : Representation ℂ (L × H) EB)
  (ρF : Representation ℂ (L × H) (JetLinear.Field F))
  (ρB : Representation ℂ (L × H) (JetLinear.Field B))
  (σ : Representation ℂ (L × H) (Direction I))
  (cF : ∀ g x, combined ρF σ g (eF x) = eF (τF g x))
  (cB : ∀ g x, combined ρB σ g (eB x) = eB (τB g x))
  (n m d : ℕ) (a : Representation ℂ H (T → ℂ)) (s : T → ℂ)

abbrev LocalCoefficients := LocalSpurionEvaluation.Coefficients
  (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s

def localCoefficientEquiv := LocalSpurionEvaluation.coefficientEquiv
  (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s

def spurionEvaluation (b : ℕ) := LocalSpurionEvaluation.evaluation
  (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s b

theorem spurion_surjective : Function.Surjective
    (spurionEvaluation eF eB τF τB ρF ρB σ cF cB n m d a s (orbitSize a s - 1)) :=
  LocalSpurionEvaluation.evaluation_surjective
    (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s

theorem spurion_card_surjective : Function.Surjective
    (spurionEvaluation eF eB τF τB ρF ρB σ cF cB n m d a s (Fintype.card H - 1)) :=
  LocalSpurionEvaluation.card_evaluation_surjective
    (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s

theorem spurion_nonzero_iff :
    (∃ f : LocalCoefficients eF eB τF τB ρF ρB σ cF cB n m d a s, f ≠ 0) ↔
      ∃ p, spurionEvaluation eF eB τF τB ρF ρB σ cF cB n m d a s (orbitSize a s - 1) p ≠ 0 :=
  LocalSpurionEvaluation.nonzero_iff (quotientAction eF eB τF τB ρF ρB σ cF cB n m d) a s

omit [Finite F] [Finite B] [Fintype H] [Fintype T] in
theorem local_pullback_injective : Function.Injective
    (fun f : LocalCoefficients eF eB τF τB ρF ρB σ cF cB n m d a s =>
      fun x : MixedJetAlgebra.grade F B I n m (d + 1) => f.val (combinedProjection eF eB n m d x)) := by
  intro f g he
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := combinedProjection_surjective eF eB n m d x
  exact congrFun he x

end
end Math.LinearJetAlgebra
