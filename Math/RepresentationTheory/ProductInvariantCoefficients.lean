import Math.RepresentationTheory.SeparatedInvariantCoefficients

/-! Product representations connect simultaneous fixed coefficient spaces
without assuming an invariant-space comparison. -/
namespace Math.ProductInvariantCoefficients
set_option autoImplicit false
noncomputable section
open Representation
variable {A B G V : Type*} [Group A] [Group B] [Group G]
  [AddCommGroup V] [Module ℂ V]
  (r : Representation ℂ (A × B) V) (rho : Representation ℂ G V) (j : A →* G)
  (sigma : Representation ℂ B V)
  (ha : r.comp (MonoidHom.inl A B) = rho.comp j)
  (hb : r.comp (MonoidHom.inr A B) = sigma)

include ha hb in
theorem fixed_iff (f : Module.Dual ℂ V) :
    (∀ g x, f (r g x) = f x) ↔ f ∈ SeparatedInvariantCoefficients.Space rho j sigma := by
  have h₁ (a : A) (x : V) : r (a,1) x = rho (j a) x :=
    LinearMap.congr_fun (congrArg (fun s => s a) ha) x
  have h₂ (b : B) (x : V) : r (1,b) x = sigma b x :=
    LinearMap.congr_fun (congrArg (fun s => s b) hb) x
  constructor
  · intro hf
    exact ⟨fun a x => (congrArg f (h₁ a x)).symm.trans (hf (a,1) x),
      fun b x => (congrArg f (h₂ b x)).symm.trans (hf (1,b) x)⟩
  · intro hf g x
    have hg : g = (g.1,1) * (1,g.2) := by simp
    rw [hg,map_mul,Module.End.mul_apply,h₁,hf.1,h₂,hf.2]

def equiv : InvariantCoefficientTransport.Invariants r ≃ₗ[ℂ]
    SeparatedInvariantCoefficients.Space rho j sigma where
  toFun f := ⟨f.toLinearMap,(fixed_iff r rho j sigma ha hb f.toLinearMap).mp
    (fun g x => f.isIntertwining _ _ g x)⟩
  invFun f :=
    { toLinearMap := f.val
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact (fixed_iff r rho j sigma ha hb f.val).mpr f.property g x }
  left_inv f := by apply IntertwiningMap.ext; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Math.ProductInvariantCoefficients
