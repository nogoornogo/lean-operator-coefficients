import Math.RepresentationTheory.InvariantCoefficientTransport

/-! Whole coefficient spaces from a retained factor and a compared invariant action. -/
namespace Math.SeparatedInvariantCoefficients
set_option autoImplicit false
noncomputable section
open Representation
variable {G B W K V : Type*} [Group G] [Group B] [Group W] [Group K]
  [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) (retained : B →* G) (spin : W →* G)
  (sigma : Representation ℂ K V)

def Space : Submodule ℂ (Module.Dual ℂ V) where
  carrier := {f | (∀ b x, f (rho (retained b) x) = f x) ∧ ∀ k x, f (sigma k x) = f x}
  zero_mem' := ⟨by intros; rfl,by intros; rfl⟩
  add_mem' := by
    intro f h hf hh
    exact ⟨by intro b x; change f _ + h _ = f x + h x; rw [hf.1,hh.1],
      by intro k x; change f _ + h _ = f x + h x; rw [hf.2,hh.2]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨by intro b x; change c • f _ = c • f x; rw [hf.1],
      by intro k x; change c • f _ = c • f x; rw [hf.2]⟩

theorem fixed_iff (hg : ∀ g, ∃ b w, g = retained b * spin w)
    (hc : ∀ f : Module.Dual ℂ V, (∀ w x, f (rho (spin w) x) = f x) ↔
      ∀ k x, f (sigma k x) = f x) (f : Module.Dual ℂ V) :
    (∀ g x, f (rho g x) = f x) ↔ f ∈ Space rho retained sigma := by
  constructor
  · intro h
    exact ⟨fun b x => h _ x,(hc f).mp (fun w x => h _ x)⟩
  · intro h g x
    obtain ⟨b,w,he⟩ := hg g
    rw [he,map_mul,Module.End.mul_apply,h.1,(hc f).mpr h.2]

def equiv (hg : ∀ g, ∃ b w, g = retained b * spin w)
    (hc : ∀ f : Module.Dual ℂ V, (∀ w x, f (rho (spin w) x) = f x) ↔
      ∀ k x, f (sigma k x) = f x) :
    InvariantCoefficientTransport.Invariants rho ≃ₗ[ℂ] Space rho retained sigma where
  toFun f := ⟨f.toLinearMap,(fixed_iff rho retained spin sigma hg hc f.toLinearMap).mp
    (fun g x => f.isIntertwining _ _ g x)⟩
  invFun f :=
    { toLinearMap := f.val
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact (fixed_iff rho retained spin sigma hg hc f.val).mpr f.property g x }
  left_inv f := by apply IntertwiningMap.ext; rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Math.SeparatedInvariantCoefficients
