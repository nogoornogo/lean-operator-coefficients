import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.LinearAlgebra.SelectionCriteria

/-! Scalar residual action separates charge neutrality from actual local
invariants. The local coefficient space is not classified by this lemma. -/
namespace Math.ScalarResidualSupport
set_option autoImplicit false
noncomputable section
open Representation
variable {G R X : Type*} [Group G] [Group R] [AddCommGroup X] [Module ℂ X]
  (rho : Representation ℂ (G × R) X) (chi : R → ℂ)
  (hs : ∀ r x, rho (1,r) x = chi r • x)

abbrev Full := InvariantCoefficientTransport.Invariants rho
abbrev Local := InvariantCoefficientTransport.Invariants (rho.comp (MonoidHom.inl G R))

def restrict (f : Full rho) : Local rho where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (g,1)

include hs in
theorem neutral_of_allowed (hf : SelectionCriteria.Allowed (Full rho)) : ∀ r, chi r=1 := by
  obtain ⟨f,hf⟩ := hf
  have hv : ∃ x, f x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (IntertwiningMap.ext (LinearMap.ext hn))
  obtain ⟨x,hx⟩ := hv
  intro r
  have he := f.isIntertwining _ _ (1,r) x
  change f (rho (1,r) x) = f x at he
  rw [hs,map_smul,smul_eq_mul] at he
  exact mul_right_cancel₀ hx (he.trans (one_mul _).symm)

include hs in
def extend (hn : ∀ r, chi r=1) (f : Local rho) : Full rho where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change f (rho g x) = f x
    have he : rho g x = rho (g.1,1) (rho (1,g.2) x) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [he,hs,hn,one_smul]
    exact f.isIntertwining _ _ g.1 x

include hs in
def equiv (hn : ∀ r, chi r=1) : Full rho ≃ₗ[ℂ] Local rho where
  toFun := restrict rho
  invFun := extend rho chi hs hn
  left_inv _ := by ext x; rfl
  right_inv _ := by ext x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hs in
theorem allowed_iff : SelectionCriteria.Allowed (Full rho) ↔
    (∀ r, chi r=1) ∧ SelectionCriteria.Allowed (Local rho) := by
  constructor
  · intro hf
    have hn := neutral_of_allowed rho chi hs hf
    exact ⟨hn,(SelectionCriteria.allowed_equiv (equiv rho chi hs hn)).mp hf⟩
  · rintro ⟨hn,hf⟩
    exact (SelectionCriteria.allowed_equiv (equiv rho chi hs hn)).mpr hf

theorem exists_guard_iff {I : Type*} (guard full localTest : I → Prop) (neutral : Prop)
    (he : ∀ i, full i ↔ neutral ∧ localTest i) :
    (∃ i, guard i ∧ full i) ↔ neutral ∧ ∃ i, guard i ∧ localTest i := by
  constructor
  · rintro ⟨i,hg,hf⟩
    obtain ⟨hn,hl⟩ := (he i).mp hf
    exact ⟨hn,i,hg,hl⟩
  · rintro ⟨hn,i,hg,hl⟩
    exact ⟨i,hg,(he i).mpr ⟨hn,hl⟩⟩

end
end Math.ScalarResidualSupport
