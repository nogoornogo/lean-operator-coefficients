import Math.RepresentationTheory.Exterior.ExteriorWeightSupport

/-! Conjugation of invariant exterior coefficients is semilinear. An
equivariant conjugation of the supplied field representation is explicit
input; neither self-duality nor a complex-linear conjugation is assumed. -/
namespace Math.ExteriorConjugation
set_option autoImplicit false
noncomputable section
open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) {n : ℕ}
  (c : V ≃ₛₗ[starRingEnd ℂ] V)
  (hc : ∀ g x, c (rho g x) = rho g (c x))

def conjugateAlternating (f : ExteriorWeightSupport.Coefficient rho (n := n)) :
    V [⋀^Fin n]→ₗ[ℂ] ℂ where
  toFun v := star (f (exteriorPower.ιMulti ℂ n (fun i => c (v i))))
  map_update_add' v i x y := by
    have h (v : Fin n → V) (x : V) : (fun j => c (Function.update v i x j)) =
        Function.update (fun j => c (v j)) i (c x) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [h, h, h, map_add]
    simp only [AlternatingMap.map_update_add, map_add, star_add]
  map_update_smul' v i z x := by
    have h (x : V) : (fun j => c (Function.update v i x j)) =
        Function.update (fun j => c (v j)) i (c x) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [h, h, c.map_smulₛₗ]
    simp only [AlternatingMap.map_update_smul, map_smul, smul_eq_mul,
      starRingEnd_apply, star_mul, star_star]
    ring
  map_eq_zero_of_eq' v i j he hij := by
    rw [(exteriorPower.ιMulti ℂ n).map_eq_zero_of_eq _ (congrArg c he) hij, map_zero, star_zero]

def conjugate (f : ExteriorWeightSupport.Coefficient rho (n := n)) :
    ExteriorWeightSupport.Coefficient rho (n := n) where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (conjugateAlternating rho c f)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change star (f (exteriorPower.ιMulti ℂ n (fun i => c (rho g (v i))))) =
      star (f (exteriorPower.ιMulti ℂ n (fun i => c (v i))))
    simp only [hc]
    have h := IntertwiningMap.isIntertwining _ _ f g
      (exteriorPower.ιMulti ℂ n (fun i => c (v i)))
    rw [Representation.exteriorPower_apply_ιMulti] at h
    exact congrArg star h

@[simp] theorem conjugate_apply (f : ExteriorWeightSupport.Coefficient rho (n := n))
    (v : Fin n → V) : conjugate rho c hc f (exteriorPower.ιMulti ℂ n v) =
    star (f (exteriorPower.ιMulti ℂ n (fun i => c (v i)))) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

variable (hi : ∀ x, c (c x) = x)

def equiv : ExteriorWeightSupport.Coefficient rho (n := n) ≃ₛₗ[starRingEnd ℂ]
    ExteriorWeightSupport.Coefficient rho (n := n) where
  toFun := conjugate rho c hc
  invFun := conjugate rho c hc
  left_inv f := by
    apply IntertwiningMap.ext
    apply exteriorPower.linearMap_ext
    ext v
    change conjugate rho c hc (conjugate rho c hc f) (exteriorPower.ιMulti ℂ n v) =
      f (exteriorPower.ιMulti ℂ n v)
    simp only [conjugate_apply, hi, star_star]
  right_inv f := by
    apply IntertwiningMap.ext
    apply exteriorPower.linearMap_ext
    ext v
    change conjugate rho c hc (conjugate rho c hc f) (exteriorPower.ιMulti ℂ n v) =
      f (exteriorPower.ιMulti ℂ n v)
    simp only [conjugate_apply, hi, star_star]
  map_add' f h := by
    apply IntertwiningMap.ext
    apply exteriorPower.linearMap_ext
    ext v
    simp [conjugate_apply]
  map_smul' z f := by
    apply IntertwiningMap.ext
    apply exteriorPower.linearMap_ext
    ext v
    simp [conjugate_apply, star_mul, mul_comm]

end
end Math.ExteriorConjugation
