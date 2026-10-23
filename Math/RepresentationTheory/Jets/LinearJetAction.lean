import Math.Algebra.Jets.LinearJetAlgebra
import Math.RepresentationTheory.Jets.DirectionalJetIBP

/-! Actual group actions and covariance on the on-shell odd/even algebra. -/
namespace Math.LinearJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections LinearJetEquation
open scoped TensorProduct

variable {F B I EF EB H : Type*} [AddCommGroup EF] [Module ℂ EF]
  [AddCommGroup EB] [Module ℂ EB] [Group H]
  (eF : EF →ₗ[ℂ] Jet F I) (eB : EB →ₗ[ℂ] Jet B I)
  (τF : Representation ℂ H EF) (τB : Representation ℂ H EB)
  (ρF : Representation ℂ H (JetLinear.Field F)) (ρB : Representation ℂ H (JetLinear.Field B))
  (σ : Representation ℂ H (Direction I))
  (cF : ∀ h x, combined ρF σ h (eF x) = eF (τF h x))
  (cB : ∀ h x, combined ρB σ h (eB x) = eB (τB h x))

def action : Representation ℂ H (Algebra eF eB) :=
  (LinearJetEquation.action eF τF ρF σ cF).exteriorAlgebra.tprod
    (PhyslibSymmetric.Representation.symmetricAlgebra (LinearJetEquation.action eB τB ρB σ cB))

theorem oddProjection_action (g : H) (x : MixedJetAlgebra.Odd F I) :
    oddProjection eF ((combined ρF σ).exteriorAlgebra g x) =
      (LinearJetEquation.action eF τF ρF σ cF).exteriorAlgebra g (oddProjection eF x) :=
  ExteriorAlgebra.algHom_exteriorAlgebra (oddProjection eF) (oddProjection_ι eF) g (fun _ => rfl) x

theorem evenProjection_action (g : H) (x : MixedJetAlgebra.Even B I) :
    evenProjection eB (JetFunctor.polynomialAction (combined ρB σ) g x) =
      PhyslibSymmetric.Representation.symmetricAlgebra (LinearJetEquation.action eB τB ρB σ cB)
        g (evenProjection eB x) := by
  have he : (evenProjection eB).comp (JetFunctor.polynomialMap (combined ρB σ g)) =
      (PhyslibSymmetric.Representation.symmetricAlgebraAlgHom
        (LinearJetEquation.action eB τB ρB σ cB) g).comp (evenProjection eB) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, JetFunctor.polynomialMap_X, evenProjection_linearForm,
      evenProjection_X, PhyslibSymmetric.Representation.symmetricAlgebraAlgHom,
      SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, LinearJetEquation.action_mk]
  exact DFunLike.congr_fun he x

theorem projection_action (g : H) (x : MixedJetAlgebra.Algebra F B I) :
    projection eF eB (JetFunctor.mixedAction (combined ρF σ) (combined ρB σ) g x) =
      action eF eB τF τB ρF ρB σ cF cB g (projection eF eB x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    change oddProjection eF ((combined ρF σ).exteriorAlgebra g x) ⊗ₜ[ℂ]
      evenProjection eB (JetFunctor.polynomialAction (combined ρB σ) g y) = _
    rw [oddProjection_action eF τF ρF σ cF, evenProjection_action eB τB ρB σ cB]
    rfl

theorem covariance [Fintype I] (g : H) (i : I) (x : Algebra eF eB) :
    action eF eB τF τB ρF ρB σ cF cB g (derivative eF eB i x) =
      ∑ j, (σ g (Finsupp.single i 1)) j • derivative eF eB j (action eF eB τF τB ρF ρB σ cF cB g x) := by
  obtain ⟨x, rfl⟩ := projection_surjective eF eB x
  rw [← projection_derivative, ← projection_action]
  rw [JetFunctor.mixed_covariant (combined ρF σ) (combined ρB σ) g i _
    (combined_covariant ρF σ g i) (combined_covariant ρB σ g i), map_sum]
  simp only [map_smul, projection_derivative, projection_action eF eB τF τB ρF ρB σ cF cB]

end
end Math.LinearJetAlgebra
