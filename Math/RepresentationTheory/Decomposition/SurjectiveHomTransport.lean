import Math.RepresentationTheory.Decomposition.RepresentationDescent

/-! Algebraic Hom transport along a surjective group homomorphism. No
dimension, compactness or continuity assumptions; underlying maps are unchanged. -/
namespace Math.SurjectiveHomTransport
set_option autoImplicit false
noncomputable section
variable {G K V W : Type*} [Group G] [Group K]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]

def homEquiv (q : G →* K) (hq : Function.Surjective q)
    (a : Representation ℂ K V) (b : Representation ℂ K W) :
    Representation.IntertwiningMap (a.comp q) (b.comp q) ≃ₗ[ℂ]
      Representation.IntertwiningMap a b where
  toFun f := ⟨f.toLinearMap, fun k => by
    obtain ⟨g, rfl⟩ := hq k
    exact f.isIntertwining' g⟩
  invFun f := ⟨f.toLinearMap, fun g => f.isIntertwining' (q g)⟩
  left_inv _ := Representation.IntertwiningMap.ext rfl
  right_inv _ := Representation.IntertwiningMap.ext rfl
  map_add' _ _ := Representation.IntertwiningMap.ext rfl
  map_smul' _ _ := Representation.IntertwiningMap.ext rfl

@[simp] theorem homEquiv_apply (q : G →* K) (hq : Function.Surjective q)
    (a : Representation ℂ K V) (b : Representation ℂ K W)
    (f : Representation.IntertwiningMap (a.comp q) (b.comp q)) :
    (homEquiv q hq a b f).toLinearMap = f.toLinearMap := rfl

theorem nonzero_iff (q : G →* K) (hq : Function.Surjective q)
    (a : Representation ℂ K V) (b : Representation ℂ K W) :
    (∃ f : Representation.IntertwiningMap (a.comp q) (b.comp q), f ≠ 0) ↔
      ∃ f : Representation.IntertwiningMap a b, f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨homEquiv q hq a b f, by simpa using hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨(homEquiv q hq a b).symm f, by simpa using hf⟩

theorem descends_iff (q : G →* K) (hq : Function.Surjective q)
    (a : Representation ℂ G V) :
    (∃ b : Representation ℂ K V, b.comp q = a) ↔ q.ker ≤ a.ker := by
  constructor
  · rintro ⟨b, rfl⟩ g hg
    change b (q g) = 1
    rw [MonoidHom.mem_ker.mp hg, map_one]
  · intro hk
    exact ⟨RepresentationDescent.descend q hq a hk,
      RepresentationDescent.descend_comp q hq a hk⟩

end
end Math.SurjectiveHomTransport
