import Physics.FieldTheory.Jets.Weyl.Equations.WeylCurrentCovariance
import Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls

/-! Necessary finite controls for two Weyl spinors and one dual vector.
Every row is derived from invariance under an actual SL(2,C) element. -/
namespace Physics.WeylDirectionInvariant
set_option autoImplicit false
noncomputable section
open Math LorentzDirections LorentzFiniteControls
abbrev Spin := JetLinear.Field (Fin 2)
abbrev Dir := JetDirections.Direction (Fin 4)
abbrev Tensor := Spin →ₗ[ℂ] Spin →ₗ[ℂ] Dir →ₗ[ℂ] ℂ
def S (a : Fin 2) : Spin := Finsupp.single a 1
def component (f : Tensor) (a b : Fin 2) (i : Fin 4) : ℂ := f (S a) (S b) (E i)
theorem component_apply (f : Tensor) (a b : Fin 2) (i : Fin 4) :
    component f a b i = f (S a) (S b) (E i) := rfl

def sample : Fin 4 → Group := ![flipZ,flipX,shear 1,shear Complex.I]
def spinRows (c : Bool) (s : Fin 4) (a b : Fin 2) : ℂ :=
  WeylCurrentCovariance.component c (sample s) b a
def directionRows (s : Fin 4) (i j : Fin 4) : ℂ :=
  if s = 0 then if i = j then signsZ i else 0 else
  if s = 1 then if i = j then signsX i else 0 else
  if s = 2 then realRows i j else imagRows i j

theorem spin_basis (c : Bool) (s : Fin 4) (a : Fin 2) :
    LorentzJetIBP.weyl c (sample s) (S a) = ∑ b : Fin 2, spinRows c s a b • S b :=
  WeylCurrentCovariance.field_components c (sample s) a

theorem direction_basis (s : Fin 4) (i : Fin 4) :
    direction (sample s) (E i) = ∑ j : Fin 4, directionRows s i j • E j := by
  fin_cases s
  · simpa [sample,directionRows] using flipZ_direction i
  · simpa [sample,directionRows] using flipX_direction i
  · simpa [sample,directionRows] using real_basis i
  · simpa [sample,directionRows] using imag_basis i

variable (c d : Bool) (f : Tensor)
  (h : ∀ g u v w, f (LorentzJetIBP.weyl c g u) (LorentzJetIBP.weyl d g v)
    (direction g w) = f u v w)

include h in
theorem row (s : Fin 4) (a b : Fin 2) (i : Fin 4) :
    (∑ j : Fin 4, ∑ v : Fin 2, ∑ u : Fin 2,
      (spinRows c s a u * spinRows d s b v * directionRows s i j) * component f u v j) -
        component f a b i = 0 := by
  have he := h (sample s) (S a) (S b) (E i)
  rw [spin_basis,spin_basis,direction_basis] at he
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul] at he
  apply sub_eq_zero.mpr
  simpa only [component,mul_assoc,mul_comm,mul_left_comm,Finset.mul_sum] using he

/-- Twice the inverse Pauli matrix coefficients, normalized at (0,0,0). -/
def kernel (a b : Fin 2) (i : Fin 4) : ℂ :=
  2 * fromPauli (Matrix.of (fun u v => if u = a ∧ v = b then 1 else 0)) i

end
end Physics.WeylDirectionInvariant
