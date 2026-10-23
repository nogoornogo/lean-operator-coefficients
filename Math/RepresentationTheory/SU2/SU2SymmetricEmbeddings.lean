import Math.RepresentationTheory.Symmetric.SymmetricPowerOperations
import Math.RepresentationTheory.SU2.WeakDoubletScalars
import Math.LinearAlgebra.Symmetric.SymmetricPowerLowDegree
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Nonzero SU2-equivariant symmetric tensor embeddings from the determinant tensor. -/
namespace Math.SU2SymmetricEmbeddings
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars SymmetricPowerOperations
open scoped TensorProduct

def e (i : Fin 2) : Doublet := Pi.single i 1

def omega : Doublet ⊗[ℂ] Doublet := e 0 ⊗ₜ[ℂ] e 1 - e 1 ⊗ₜ[ℂ] e 0

theorem omega_invariant (g : Group) : (doublet.tprod doublet) g omega = omega := by
  apply ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).repr.injective
  ext ij
  rcases ij with ⟨i,j⟩
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := g.prop.2
  rw [Matrix.det_fin_two] at hd
  fin_cases i <;> fin_cases j <;>
    simp [omega,e,Representation.tprod_apply,Module.Basis.tensorProduct_repr_tmul_apply,
      doublet,TauCeti.stdRep,TauCeti.SU2.toGL] <;>
      first | (solve | ring) | (solve | linear_combination hd) | (solve | linear_combination -hd)

def oneTransport : IntertwiningMap (doublet.tprod doublet)
    ((doublet.symmetricPower 1).tprod (doublet.symmetricPower 1)) :=
  { toLinearMap := TensorProduct.map SymmetricPowerLowDegree.inclusion SymmetricPowerLowDegree.inclusion
    isIntertwining' g := by
      apply TensorProduct.ext'
      intro v w
      change SymmetricPowerLowDegree.inclusion (doublet g v) ⊗ₜ[ℂ]
        SymmetricPowerLowDegree.inclusion (doublet g w) =
        ((doublet.symmetricPower 1).tprod (doublet.symmetricPower 1)) g
          (SymmetricPowerLowDegree.inclusion v ⊗ₜ[ℂ] SymmetricPowerLowDegree.inclusion w)
      simp only [SymmetricPowerLowDegree.inclusion_apply,Representation.tprod_apply,
        TensorProduct.map_tmul,Representation.symmetricPower_apply_tprod] }

def omegaOne : Sym[ℂ]^1 Doublet ⊗[ℂ] Sym[ℂ]^1 Doublet := oneTransport omega

theorem omegaOne_invariant (g : Group) :
    ((doublet.symmetricPower 1).tprod (doublet.symmetricPower 1)) g omegaOne = omegaOne := by
  have he := oneTransport.isIntertwining _ _ g omega
  rw [omega_invariant] at he
  exact he.symm

def omegaPower : (r : ℕ) → Sym[ℂ]^r Doublet ⊗[ℂ] Sym[ℂ]^r Doublet
  | 0 => SymmetricPower.tprod ℂ (fun i : Fin 0 => Fin.elim0 i) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun i : Fin 0 => Fin.elim0 i)
  | r+1 => blockMultiply r r 1 1 (omegaPower r ⊗ₜ[ℂ] omegaOne)

theorem omegaPower_invariant (r : ℕ) (g : Group) :
    ((doublet.symmetricPower r).tprod (doublet.symmetricPower r)) g (omegaPower r) = omegaPower r := by
  induction r with
  | zero =>
    simp only [omegaPower,Representation.tprod_apply,TensorProduct.map_tmul,
      Representation.symmetricPower_apply_tprod]
    congr 1 <;> congr 1 <;> funext i <;> exact Fin.elim0 i
  | succ r ih =>
    have he := (blockMultiplication doublet r r 1 1).isIntertwining _ _ g
      (omegaPower r ⊗ₜ[ℂ] omegaOne)
    change blockMultiply r r 1 1
      (((doublet.symmetricPower r).tprod (doublet.symmetricPower r)) g (omegaPower r) ⊗ₜ[ℂ]
        ((doublet.symmetricPower 1).tprod (doublet.symmetricPower 1)) g omegaOne) =
      ((doublet.symmetricPower (r+1)).tprod (doublet.symmetricPower (r+1))) g
        (blockMultiply r r 1 1 (omegaPower r ⊗ₜ[ℂ] omegaOne)) at he
    rw [ih,omegaOne_invariant] at he
    exact he.symm

def phi : Module.Dual ℂ Doublet := LinearMap.proj 0
def psi : Module.Dual ℂ Doublet := LinearMap.proj 1

theorem omegaOne_evaluation : biEval 1 1 phi psi omegaOne = 1 := by
  change biEval 1 1 phi psi
    (TensorProduct.map SymmetricPowerLowDegree.inclusion SymmetricPowerLowDegree.inclusion
      (e 0 ⊗ₜ[ℂ] e 1 - e 1 ⊗ₜ[ℂ] e 0)) = 1
  simp [phi,psi,e]

theorem omegaPower_evaluation (r : ℕ) : biEval r r phi psi (omegaPower r) = 1 := by
  induction r with
  | zero => simp [omegaPower]
  | succ r ih =>
    rw [omegaPower,biEval_blockMultiply,ih,omegaOne_evaluation,mul_one]

def insert (p q r : ℕ) : IntertwiningMap
    ((doublet.symmetricPower p).tprod (doublet.symmetricPower q))
    ((doublet.symmetricPower (p+r)).tprod (doublet.symmetricPower (q+r))) where
  toLinearMap := (blockMultiply p q r r).comp
    ((TensorProduct.mk ℂ _ _).flip (omegaPower r))
  isIntertwining' g := by
    ext v w
    have he := (blockMultiplication doublet p q r r).isIntertwining _ _ g
      ((SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) ⊗ₜ[ℂ] omegaPower r)
    change blockMultiply p q r r
      ((((doublet.symmetricPower p).tprod (doublet.symmetricPower q)) g
        (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)) ⊗ₜ[ℂ]
        (((doublet.symmetricPower r).tprod (doublet.symmetricPower r)) g (omegaPower r))) =
      ((doublet.symmetricPower (p+r)).tprod (doublet.symmetricPower (q+r))) g
        (blockMultiply p q r r
          ((SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) ⊗ₜ[ℂ] omegaPower r)) at he
    rw [omegaPower_invariant] at he
    exact he

def embedding (p q r : ℕ) : IntertwiningMap (doublet.symmetricPower (p+q))
    ((doublet.symmetricPower (p+r)).tprod (doublet.symmetricPower (q+r))) :=
  (insert p q r).comp (splitting doublet p q)

def probe : Doublet := fun _ => 1

theorem embedding_evaluation (p q r : ℕ) :
    biEval (p+r) (q+r) phi psi
      (embedding p q r (SymmetricPower.tprod ℂ (fun _ => probe))) = 1 := by
  change biEval (p+r) (q+r) phi psi (blockMultiply p q r r
    (split p q (SymmetricPower.tprod ℂ (fun _ => probe)) ⊗ₜ[ℂ] omegaPower r)) = 1
  rw [split_diagonal,biEval_blockMultiply,omegaPower_evaluation,biEval_pure,
    powerEval_diagonal,powerEval_diagonal]
  simp [phi,psi,probe]

theorem embedding_nonzero (p q r : ℕ) : embedding p q r ≠ 0 := by
  intro he
  have hv := embedding_evaluation p q r
  rw [he] at hv
  simp at hv

theorem embedding_injective (p q r : ℕ) : Function.Injective (embedding p q r) :=
by
  have hh := IsIrreducible.injective_or_eq_zero
    (W := Sym[ℂ]^(p+r) Doublet ⊗[ℂ] Sym[ℂ]^(q+r) Doublet) (embedding p q r)
  exact hh.resolve_right (embedding_nonzero p q r)

end
end Math.SU2SymmetricEmbeddings
