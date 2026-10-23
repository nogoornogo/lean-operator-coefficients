import Math.RepresentationTheory.Jets.JetFunctor

/-! A finite component/conjugate label pair represents a module and its dual.
No physical conjugation is inferred for an arbitrary representation. -/
namespace Math.PairedComponentFields
set_option autoImplicit false
noncomputable section
open Representation
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Group H]
abbrev V (ι : Type*) := ι → ℂ

def dualCoordinates : V ι ≃ₗ[ℂ] Module.Dual ℂ (V ι) where
  toFun v := {
    toFun x := ∑ i, v i*x i
    map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
    map_smul' c x := by
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring }
  invFun f i := f (Pi.single i 1)
  left_inv v := by ext i; simp [Pi.single_apply]
  right_inv f := by
    apply LinearMap.ext
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1:ℂ) := by ext i; simp [Pi.single_apply]
    conv_rhs => rw [hx,map_sum]
    simp only [map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change (∑ i, (v i+w i)*x i) = (∑ i, v i*x i)+(∑ i, w i*x i)
    simp [add_mul,Finset.sum_add_distrib]
  map_smul' c v := by
    apply LinearMap.ext
    intro x
    change (∑ i, (c*v i)*x i) = c*(∑ i, v i*x i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def split : (Bool × ι → ℂ) ≃ₗ[ℂ] V ι × V ι where
  toFun v := (fun i => v (false,i),fun i => v (true,i))
  invFun v j := if j.1 then v.2 j.2 else v.1 j.2
  left_inv v := by funext j; obtain ⟨c,i⟩ := j; cases c <;> rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fieldEquiv : JetLinear.Field (Bool × ι) ≃ₗ[ℂ] V ι × Module.Dual ℂ (V ι) :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ (Bool × ι)).trans
    (split.trans ((LinearEquiv.refl ℂ (V ι)).prodCongr dualCoordinates))

theorem dual_basis (i : ι) (v : V ι) : dualCoordinates (Pi.single i 1) v = v i := by
  simp [dualCoordinates,Pi.single_apply]

theorem fieldEquiv_false (i : ι) :
    fieldEquiv (Finsupp.single (false,i) 1) = (Pi.single i 1,0) := by
  apply Prod.ext
  · funext j
    change Finsupp.single (false,i) (1:ℂ) (false,j) = (Pi.single i (1:ℂ) : V ι) j
    simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
  · apply LinearMap.ext
    intro x
    change (∑ j, (Finsupp.single (false,i) (1:ℂ) (true,j))*x j) = 0
    simp

theorem fieldEquiv_true (i : ι) :
    fieldEquiv (Finsupp.single (true,i) 1) = (0,dualCoordinates (Pi.single i 1)) := by
  apply Prod.ext
  · funext j
    change Finsupp.single (true,i) (1:ℂ) (false,j) = 0
    simp
  · change dualCoordinates (fun j => Finsupp.single (true,i) (1:ℂ) (true,j)) = _
    apply congrArg dualCoordinates
    funext j
    simp [Finsupp.single_apply,Pi.single_apply,eq_comm]

def action (rho : Representation ℂ H (V ι)) :
    Representation ℂ H (JetLinear.Field (Bool × ι)) :=
  fieldEquiv.symm.conjRingEquiv.toMonoidHom.comp (rho.prod rho.dual)

theorem fieldEquiv_action (rho : Representation ℂ H (V ι)) (g : H)
    (v : JetLinear.Field (Bool × ι)) :
    fieldEquiv (action rho g v) =
      (rho g (fieldEquiv v).1,rho.dual g (fieldEquiv v).2) := by
  change fieldEquiv (fieldEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

def contraction (v : JetLinear.Field (Bool × ι)) : ℂ :=
  (fieldEquiv v).2 (fieldEquiv v).1

theorem contraction_invariant (rho : Representation ℂ H (V ι)) (g : H)
    (v : JetLinear.Field (Bool × ι)) : contraction (action rho g v) = contraction v := by
  simp only [contraction,fieldEquiv_action]
  change (fieldEquiv v).2 (rho g⁻¹ (rho g (fieldEquiv v).1)) = _
  rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]

end
end Math.PairedComponentFields
