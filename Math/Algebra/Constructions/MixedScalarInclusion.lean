import Math.RepresentationTheory.Jets.JetFunctor
import Math.Algebra.Jets.TwoSidedDifferentialRelations

/-! The scalar jet algebra embeds as the even factor. Full differential
equation closure transports through this map; divergences stay linear. -/
namespace Math.MixedScalarInclusion
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {F B I H : Type*}

def embed : ScalarJetAlgebra.Algebra B I →ₐ[ℂ] MixedJetAlgebra.Algebra F B I :=
  Algebra.TensorProduct.includeRight

theorem derivative (i : I) (p : ScalarJetAlgebra.Algebra B I) :
    MixedJetAlgebra.totalDerivative i (embed (F := F) p) =
      embed (ScalarJetAlgebra.totalDerivative i p) := by
  simp [embed, Algebra.TensorProduct.includeRight_apply,
    MixedJetAlgebra.oddDerivative]

theorem natural [Monoid H] (f : Representation ℂ H (JetLinear.Jet F I))
    (b : Representation ℂ H (JetLinear.Jet B I)) (g : H)
    (p : ScalarJetAlgebra.Algebra B I) :
    JetFunctor.mixedAction f b g (embed p) =
      embed (JetFunctor.polynomialAction b g p) := by
  change ExteriorAlgebra.map (f g) 1 ⊗ₜ[ℂ] JetFunctor.polynomialMap (b g) p = _
  rw [map_one]
  rfl

theorem equations (R : Set (ScalarJetAlgebra.Algebra B I))
    (S : Set (MixedJetAlgebra.Algebra F B I))
    (h : ∀ p ∈ R, embed p ∈ TwoSidedDifferential.relations
      MixedJetAlgebra.totalDerivative S) :
    ∀ p ∈ TwoSidedDifferential.relations
      (fun i => (ScalarJetAlgebra.totalDerivative i).toLinearMap) R,
      embed p ∈ TwoSidedDifferential.relations MixedJetAlgebra.totalDerivative S := by
  intro p hp
  induction hp with
  | seed p hp => exact h p hp
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add hp hq ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul a hp ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih
  | left a hp ih => rw [map_mul]; exact TwoSidedDifferential.left_mem _ _ _ ih
  | right a hp ih => rw [map_mul]; exact TwoSidedDifferential.right_mem _ _ _ ih
  | derivative i hp ih =>
    change embed (ScalarJetAlgebra.totalDerivative i _) ∈ _
    rw [← derivative]
    exact TwoSidedDifferential.derivative_mem _ _ i ih

end
end Math.MixedScalarInclusion
