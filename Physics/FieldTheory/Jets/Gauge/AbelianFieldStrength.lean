import Physics.FieldTheory.Jets.Lorentz.LorentzDirections
import Math.Algebra.Jets.JetCombined
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Ordered-pair field-strength sources and the actual Lorentz metric bridge.
Antisymmetry is imposed by the equation package, rather than assumed as data. -/
namespace Physics.AbelianFieldStrength
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections LorentzDirections
open scoped TensorProduct BigOperators

abbrev V := Coordinates
abbrev Component := Fin 4 × Fin 4
abbrev Jets := Jet Component (Fin 4)
abbrev Pair := V ⊗[ℂ] V
abbrev Triple := V ⊗[ℂ] (V ⊗[ℂ] V)

def basis (i : Fin 4) : V := Pi.single i 1
def sign (i : Fin 4) : ℂ := if i = 0 then 1 else -1

def pairBasis : Module.Basis Component ℂ Pair :=
  (Pi.basisFun ℂ (Fin 4)).tensorProduct (Pi.basisFun ℂ (Fin 4))

def pair : V →ₗ[ℂ] V →ₗ[ℂ] JetLinear.Field Component :=
  (TensorProduct.mk ℂ V V).compr₂ pairBasis.repr.toLinearMap

@[simp] theorem pair_apply (v w : V) (a b : Fin 4) : pair v w (a, b) = v a * w b := by
  simp [pair, pairBasis, mul_comm]

@[simp] theorem pair_basis (a b : Fin 4) : pair (basis a) (basis b) = Finsupp.single (a, b) 1 := by
  classical
  ext ⟨i, j⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [pair_apply, basis, Prod.mk.injEq, hi, hj]

def field : Representation ℂ Group (JetLinear.Field Component) :=
  pairBasis.repr.conjRingEquiv.toMonoidHom.comp (vector.tprod vector)

theorem field_pair (g : Group) (v w : V) : field g (pair v w) = pair (vector g v) (vector g w) := by
  change pairBasis.repr (TensorProduct.map (vector g) (vector g)
    (pairBasis.repr.symm (pairBasis.repr (v ⊗ₜ[ℂ] w)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  rfl

def form : V →ₗ[ℂ] V →ₗ[ℂ] ℂ where
  toFun v := {
    toFun w := v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3
    map_add' w z := by simp; ring
    map_smul' c w := by simp; ring }
  map_add' v w := by ext z; simp; ring
  map_smul' c v := by ext z; simp; ring

theorem form_invariant (g : Group) (v w : V) : form (vector g v) (vector g w) = form v w := by
  have h := quadratic_invariant g (v + w)
  have hv := quadratic_invariant g v
  have hw := quadratic_invariant g w
  rw [map_add] at h
  dsimp [quadratic] at h hv hw
  change vector g v 0 * vector g w 0 - vector g v 1 * vector g w 1 -
    vector g v 2 * vector g w 2 - vector g v 3 * vector g w 3 = _
  change _ = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3
  linear_combination (1/2 : ℂ) * h - (1/2 : ℂ) * hv - (1/2 : ℂ) * hw

def metric : V →ₗ[ℂ] Direction (Fin 4) := dualEquiv.toLinearMap.comp form

theorem metric_apply (v : V) (i : Fin 4) : metric v i = sign i * v i := by
  change (dualEquiv (form v)) i = _
  simp only [dualEquiv, Module.Basis.dualBasis_repr]
  fin_cases i <;> simp [form, sign, Pi.basisFun_apply]

theorem metric_covariant (g : Group) (v : V) : metric (vector g v) = direction g (metric v) := by
  change dualEquiv (form (vector g v)) =
    dualEquiv (vector.dual g (dualEquiv.symm (dualEquiv (form v))))
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg dualEquiv
  apply LinearMap.ext
  intro w
  change form (vector g v) w = form v (vector g⁻¹ w)
  have h := form_invariant g v (vector g⁻¹ w)
  have hi : vector g (vector g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rwa [hi] at h

theorem metric_basis (i : Fin 4) : metric (basis i) = sign i • Finsupp.single i 1 := by
  classical
  ext j
  by_cases h : j = i <;> simp [metric_apply, basis, h]

def directional (v : Direction (Fin 4)) : Jets →ₗ[ℂ] Jets :=
  ∑ i : Fin 4, v i • JetLinear.shift i

def directionalMap : Direction (Fin 4) →ₗ[ℂ] Jets →ₗ[ℂ] Jets where
  toFun := directional
  map_add' v w := by simp [directional, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [directional, smul_smul, Finset.smul_sum]

theorem directional_apply (v : Direction (Fin 4)) (x : Jets) :
    directional v x = ∑ i : Fin 4, v i • JetLinear.shift i x := by simp [directional]

theorem directional_single (i : Fin 4) (x : Jets) :
    directional (Finsupp.single i 1) x = JetLinear.shift i x := by
  classical
  simp [directional_apply, Finsupp.single_apply]

def zeroPair (v w : V) : Jets := atOrder 0 (pair v w)

theorem zeroPair_covariant (g : Group) (v w : V) :
    combined field direction g (zeroPair v w) = zeroPair (vector g v) (vector g w) := by
  rw [zeroPair, combined_zero, field_pair]
  rfl

theorem directional_covariant (g : Group) (v : Direction (Fin 4)) (x : Jets) :
    combined field direction g (directional v x) =
      directional (direction g v) (combined field direction g x) := by
  rw [directional_apply, map_sum]
  simp only [map_smul, combined_covariant, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, directional_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hv : v = ∑ i : Fin 4, v i • Finsupp.single i (1 : ℂ) := by
    ext i
    simp
  conv_rhs => rw [hv, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_smul]

theorem vector_expand (v : V) : ∑ i : Fin 4, v i • basis i = v := by
  classical
  ext i
  simp [basis, Pi.single_apply]

theorem canonical_identity (g : Group) (j : Fin 4) :
    ∑ i : Fin 4, (direction g (Finsupp.single i 1)) j • vector g (basis i) = basis j := by
  simp only [direction_single, ← map_smul, ← map_sum]
  rw [vector_expand, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end
end Physics.AbelianFieldStrength
