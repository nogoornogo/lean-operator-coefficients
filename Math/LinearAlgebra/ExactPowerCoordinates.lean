import Math.LinearAlgebra.GaussianRational
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.SymmetricPower.Coordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite minors and monomial coordinates for exact exterior/symmetric actions. -/
namespace Math.ExactPowerCoordinates
set_option autoImplicit false
noncomputable section
open GaussianRational
open scoped BigOperators
variable {I V : Type*} [LinearOrder I] [Fintype I] [AddCommGroup V] [Module ℂ V]

def exteriorMatrix (n : ℕ) (A : Matrix I I Scalar) :
    Matrix (Set.powersetCard I n) (Set.powersetCard I n) Scalar := fun s t =>
  Matrix.det (fun i j : Fin n => A (Set.powersetCard.ofFinEmbEquiv.symm s j)
    (Set.powersetCard.ofFinEmbEquiv.symm t i))

omit [Fintype I] in
theorem exterior_coordinate (n : ℕ) (b : Module.Basis I ℂ V)
    (f : V →ₗ[ℂ] V) (A : Matrix I I Scalar)
    (hf : ∀ i j, b.repr (f (b i)) j = embed (A j i))
    (s t : Set.powersetCard I n) :
    (b.exteriorPower n).repr (exteriorPower.map n f (b.exteriorPower n t)) s =
      embed (exteriorMatrix n A s t) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  change Matrix.det (fun i j : Fin n => b.repr (f (b (Set.powersetCard.ofFinEmbEquiv.symm t i)))
    (Set.powersetCard.ofFinEmbEquiv.symm s j)) = _
  simp only [hf]
  exact (RingHom.map_det embed.toRingHom _).symm

def symmetricMatrix (m : ℕ) (A : Matrix (Fin 2) (Fin 2) Scalar) :
    Matrix (Sym (Fin 2) m) (Sym (Fin 2) m) Scalar :=
  LinearMap.toMatrix ((Pi.basisFun Scalar (Fin 2)).symmetricPower m)
    ((Pi.basisFun Scalar (Fin 2)).symmetricPower m) (SymmetricPower.map (Matrix.toLin' A))

theorem symmetric_map (m : ℕ) (A : Matrix (Fin 2) (Fin 2) Scalar)
    (s t : Sym (Fin 2) m) :
    ((Pi.basisFun ℂ (Fin 2)).symmetricPower m).repr
      (SymmetricPower.map (Matrix.toLin' (A.map embed))
        ((Pi.basisFun ℂ (Fin 2)).symmetricPower m t)) s = embed (symmetricMatrix m A s t) := by
  classical
  obtain ⟨v,rfl⟩ := TauCeti.Sym.ofFn_surjective t
  simp only [symmetricMatrix, LinearMap.toMatrix_apply, Module.Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn, SymmetricPower.map_tprod]
  simp only [SymmetricPower.repr_basis_symmetricPower_tprod, Pi.basisFun_repr,
    Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single, Matrix.map_apply,
    map_sum, map_prod, MulOpposite.op_one, one_smul, Matrix.col_apply]

/-- A finite sum formula independent of any chosen algebraic coordinates. -/
def symmetricFormula (m : ℕ) (A : Matrix (Fin 2) (Fin 2) Scalar)
    (s t : Sym (Fin 2) m) : Scalar :=
  (∑ v ∈ {v : Fin m → Fin 2 | TauCeti.Sym.ofFn v = t},
    ∑ p ∈ {p : Fin m → Fin 2 | TauCeti.Sym.ofFn p = s}, ∏ i, A (p i) (v i)) /
      ((Finset.univ.filter (fun v : Fin m → Fin 2 => TauCeti.Sym.ofFn v = t)).card : Scalar)

theorem symmetricFormula_eq (m : ℕ) (A : Matrix (Fin 2) (Fin 2) Scalar)
    (s t : Sym (Fin 2) m) : symmetricFormula m A s t = symmetricMatrix m A s t := by
  classical
  let F : Finset (Fin m → Fin 2) := Finset.univ.filter (fun v => TauCeti.Sym.ofFn v = t)
  have hn : F.Nonempty := by
    obtain ⟨v,hv⟩ := TauCeti.Sym.ofFn_surjective t
    exact ⟨v, by simp [F,hv]⟩
  have hc : (F.card : Scalar) ≠ 0 := by
    intro h
    have he : (F.card : ℂ) = 0 := by simpa only [map_natCast,map_zero] using congrArg embed h
    exact (Nat.ne_of_gt (Finset.card_pos.mpr hn)) (Nat.cast_eq_zero.mp he)
  have he : ∀ v ∈ F,
      (∑ p ∈ {p : Fin m → Fin 2 | TauCeti.Sym.ofFn p = s}, ∏ i, A (p i) (v i)) =
        symmetricMatrix m A s t := by
    intro v hv
    have ht : TauCeti.Sym.ofFn v = t := by simpa only [F,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    rw [← ht]
    simp only [symmetricMatrix,LinearMap.toMatrix_apply,Module.Basis.symmetricPower_apply,
      SymmetricPower.tprodOfSym_ofFn,SymmetricPower.map_tprod,
      SymmetricPower.repr_basis_symmetricPower_tprod,Pi.basisFun_repr,Pi.basisFun_apply,
      Matrix.toLin'_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply]
  unfold symmetricFormula
  change (∑ v ∈ F, _) / (F.card : Scalar) = _
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hc

end
end Math.ExactPowerCoordinates
