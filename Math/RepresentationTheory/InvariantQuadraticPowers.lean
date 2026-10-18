import TauCeti.RepresentationTheory.SymmetricPower
import TauCeti.LinearAlgebra.SymmetricPower.Lift
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Perm.Fin

namespace Math.InvariantQuadraticPowers
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def paired (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) : MultilinearMap ℂ (fun _ : Fin 2 => A) ℂ where
  toFun x := q (x 0) (x 1)
  map_update_add' {hDecEq} x i v w := by fin_cases i <;> simp
  map_update_smul' {hDecEq} x i z v := by fin_cases i <;> simp

def base (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ) :
    MultilinearMap ℂ (fun _ : Fin (r*2) => A) ℂ :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin r) ℂ).compMultilinearMap (fun _ => paired q)).domDomCongr
    ((Equiv.sigmaEquivProd (Fin r) (Fin 2)).trans finProdFinEquiv)

def symmetrized (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ) :
    MultilinearMap ℂ (fun _ : Fin (r*2) => A) ℂ :=
  ∑ e : Equiv.Perm (Fin (r*2)), (base q r).domDomCongr e

theorem symmetric (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ)
    (e : Equiv.Perm (Fin (r*2))) : (symmetrized q r).domDomCongr e = symmetrized q r := by
  ext x
  simp only [symmetrized,MultilinearMap.domDomCongr_apply,sum_apply]
  exact Equiv.sum_comp (Equiv.mulLeft e) (fun t => base q r (fun i => x (t i)))

def coefficient (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ) : Sym[ℂ]^(r*2) A →ₗ[ℂ] ℂ :=
  SymmetricPower.lift (symmetrized q r) (symmetric q r)

theorem diagonal (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ) (v : A) :
    coefficient q r (SymmetricPower.tprod ℂ (fun _ => v)) =
      (Fintype.card (Equiv.Perm (Fin (r*2))) : ℂ) * (q v v)^r := by
  simp [coefficient,symmetrized,base,paired,MultilinearMap.domDomCongr_apply,
    MultilinearMap.compMultilinearMap_apply,MultilinearMap.mkPiAlgebra_apply,Sigma.curry]

theorem nonzero (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) (r : ℕ) (v : A) (hv : q v v ≠ 0) :
    coefficient q r ≠ 0 := by
  intro h
  have he := congrArg (fun f : Sym[ℂ]^(r*2) A →ₗ[ℂ] ℂ =>
    f (SymmetricPower.tprod ℂ (fun _ => v))) h
  rw [diagonal] at he
  have hc : (Fintype.card (Equiv.Perm (Fin (r*2))) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_ne_zero hc (pow_ne_zero r hv)) he

variable {G : Type*} [Group G] (rho : Representation ℂ G A)
  (q : A →ₗ[ℂ] A →ₗ[ℂ] ℂ)
  (hq : ∀ g x y, q (rho g x) (rho g y) = q x y)

include hq in
theorem base_invariant (r : ℕ) (g : G) (x : Fin (r*2) → A) :
    base q r (fun i => rho g (x i)) = base q r x := by
  simp only [base,MultilinearMap.domDomCongr_apply,MultilinearMap.compMultilinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply,paired]
  apply Finset.prod_congr rfl
  intro i _
  exact hq g _ _

include hq in
theorem symmetrized_invariant (r : ℕ) (g : G) (x : Fin (r*2) → A) :
    symmetrized q r (fun i => rho g (x i)) = symmetrized q r x := by
  simp only [symmetrized,sum_apply,MultilinearMap.domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro e _
  exact base_invariant rho q hq r g (fun i => x (e i))

def invariant (r : ℕ) : IntertwiningMap (rho.symmetricPower (r*2)) (trivial ℂ G ℂ) where
  toLinearMap := coefficient q r
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro x
    change coefficient q r (rho.symmetricPower (r*2) g (SymmetricPower.tprod ℂ x)) =
      coefficient q r (SymmetricPower.tprod ℂ x)
    rw [Representation.symmetricPower_apply_tprod]
    simp only [coefficient,SymmetricPower.lift_tprod]
    exact symmetrized_invariant rho q hq r g x

theorem invariant_nonzero (r : ℕ) (v : A) (hv : q v v ≠ 0) :
    invariant rho q hq r ≠ 0 := by
  intro h
  have hh := congrArg IntertwiningMap.toLinearMap h
  exact nonzero q r v hv hh
end
end Math.InvariantQuadraticPowers
