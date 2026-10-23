import Math.Algebra.Jets.JetConjugation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Real coefficient controls for a self-adjoint line and an independent
conjugate pair. These are real modules, not complex submodules. -/
namespace Math.HermitianCoefficientChecks
set_option autoImplicit false
noncomputable section

def realLine : Submodule ℝ ℂ where
  carrier := {c | star c = c}
  zero_mem' := by simp
  add_mem' hc hd := by simpa [map_add] using congrArg₂ (·+·) hc hd
  smul_mem' a c hc := by simpa [star_smul] using congrArg (a • ·) hc

def realLineEquiv : realLine ≃ₗ[ℝ] ℝ where
  toFun c := c.val.re
  invFun a := ⟨(a : ℂ),by change star (a : ℂ) = (a : ℂ); simp⟩
  left_inv c := Subtype.ext (Complex.conj_eq_iff_re.mp c.property)
  right_inv a := Complex.ofReal_re a
  map_add' _ _ := rfl
  map_smul' a c := by
    change (a • c.val).re = a • c.val.re
    exact Complex.smul_re a c.val

def pairConjugation : (ℂ × ℂ) →ₛₗ[starRingEnd ℂ] (ℂ × ℂ) where
  toFun p := (star p.2,star p.1)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

theorem pair_involutive (p : ℂ × ℂ) : pairConjugation (pairConjugation p) = p := by
  ext <;> simp [pairConjugation]

theorem pair_fixed_iff (p : ℂ × ℂ) : pairConjugation p = p ↔ p.2 = star p.1 := by
  constructor
  · intro h
    exact (congrArg Prod.snd h).symm
  · intro h
    ext <;> simp [pairConjugation,h]

def fixedPair : Submodule ℝ (ℂ × ℂ) where
  carrier := {p | p.2 = star p.1}
  zero_mem' := by simp
  add_mem' hp hq := by change _+_ = star (_+_); rw [star_add,hp,hq]
  smul_mem' a p hp := by
    change p.2 = star p.1 at hp
    change a • p.2 = star (a • p.1)
    simp [hp]

def fixedPairEquiv : fixedPair ≃ₗ[ℝ] ℂ where
  toFun p := p.val.1
  invFun c := ⟨(c,star c),rfl⟩
  left_inv p := Subtype.ext (Prod.ext rfl p.property.symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem real_line_dimension : Module.finrank ℝ realLine = 1 := by
  rw [realLineEquiv.finrank_eq]
  exact Module.finrank_self ℝ

theorem pair_real_dimension : Module.finrank ℝ fixedPair = 2 := by
  rw [fixedPairEquiv.finrank_eq]
  exact Complex.finrank_real_complex

end
end Math.HermitianCoefficientChecks
