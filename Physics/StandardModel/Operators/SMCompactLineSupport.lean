import Math.RepresentationTheory.ContinuousLineActions
import Physics.StandardModel.Operators.SMCombinedChargeSupport

/-! Continuous lines on the compact SM group have only a hypercharge action.
This constructs actual invariant coefficients when that character is trivial. -/
namespace GUT.SMCompactLineSupport
set_option autoImplicit false
noncomputable section
open Math Representation ContinuousRepresentationScope

def color : Matrix.specialUnitaryGroup (Fin 3) ℂ →ₜ* SMCombinedCompactAction.Group where
  toMonoidHom :=
    { toFun c := ((c,(1,1)),(1,1))
      map_one' := rfl
      map_mul' _ _ := by simp }
  continuous_toFun := (continuous_id.prodMk continuous_const).prodMk continuous_const

def weak : TauCeti.SU2 →ₜ* SMCombinedCompactAction.Group where
  toMonoidHom :=
    { toFun u := ((1,(u,1)),(1,1))
      map_one' := rfl
      map_mul' _ _ := by simp }
  continuous_toFun := (continuous_const.prodMk (continuous_id.prodMk continuous_const)).prodMk continuous_const

def left : TauCeti.SU2 →ₜ* SMCombinedCompactAction.Group where
  toMonoidHom :=
    { toFun u := ((1,(1,1)),(u,1))
      map_one' := rfl
      map_mul' _ _ := by simp }
  continuous_toFun := continuous_const.prodMk (continuous_id.prodMk continuous_const)

def right : TauCeti.SU2 →ₜ* SMCombinedCompactAction.Group where
  toMonoidHom :=
    { toFun u := ((1,(1,1)),(1,u))
      map_one' := rfl
      map_mul' _ _ := by simp }
  continuous_toFun := continuous_const.prodMk (continuous_const.prodMk continuous_id)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ SMCombinedCompactAction.Group V)
  (hr : IsJointlyContinuous rho) (hd : Module.finrank ℂ V=1)

include hr hd

theorem semisimple_action (g : SMGenerationCauchy.Group) :
    rho (SMGenerationCauchy.inclusion g)=LinearMap.id := by
  have hg : SMGenerationCauchy.inclusion g = color g.1 * weak g.2.1 * left g.2.2.1 * right g.2.2.2 := by
    change ((g.1,(g.2.1,1)),g.2.2) = ((g.1,(1,1)),(1,1)) *
      ((1,(g.2.1,1)),(1,1)) * ((1,(1,1)),(g.2.2.1,1)) * ((1,(1,1)),(1,g.2.2.2))
    simp only [Prod.mul_def,mul_one,one_mul]
  have hc := ContinuousLineActions.su3 (rho.comp color.toMonoidHom) (hr.comp color) hd g.1
  have hw := ContinuousLineActions.su2 (rho.comp weak.toMonoidHom) (hr.comp weak) hd g.2.1
  have hl := ContinuousLineActions.su2 (rho.comp left.toMonoidHom) (hr.comp left) hd g.2.2.1
  have hh := ContinuousLineActions.su2 (rho.comp right.toMonoidHom) (hr.comp right) hd g.2.2.2
  change rho (color g.1)=LinearMap.id at hc
  change rho (weak g.2.1)=LinearMap.id at hw
  change rho (left g.2.2.1)=LinearMap.id at hl
  change rho (right g.2.2.2)=LinearMap.id at hh
  rw [hg,map_mul,map_mul,map_mul,hc,hw,hl,hh]
  rfl

theorem action_trivial (hh : ∀ z, rho (SMCombinedChargeSupport.hyper z)=LinearMap.id)
    (g : SMCombinedCompactAction.Group) : rho g=LinearMap.id := by
  rw [SMCombinedChargeSupport.decomposition g,map_mul,semisimple_action rho hr hd,hh]
  rfl

theorem allowed (hh : ∀ z, rho (SMCombinedChargeSupport.hyper z)=LinearMap.id) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants rho) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let f : InvariantCoefficientTransport.Invariants rho :=
    { toLinearMap := phi
      isIntertwining' g := by
        rw [action_trivial rho hr hd hh g]
        rfl }
  refine ⟨f,?_⟩
  intro hz
  have he := DFunLike.congr_fun hz v
  change phi v=0 at he
  rw [hphi] at he
  exact one_ne_zero he

end
end GUT.SMCompactLineSupport
