import Math.RepresentationTheory.Constructions.MixedPowerDescent
import TauCeti.LinearAlgebra.SymmetricPower.Basis
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! The actual symmetric tensor source and homogeneous polynomial presentation
on a free module, including the inverse and evaluation on arbitrary vectors. -/
namespace Math.SymmetricPolynomialPower
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open MvPolynomial

variable {K : Type*}

def linearForm : (K →₀ ℂ) →ₗ[ℂ] MvPolynomial K ℂ := Finsupp.linearCombination ℂ X

def equiv (n : ℕ) : Sym[ℂ]^n (K →₀ ℂ) ≃ₗ[ℂ] homogeneousSubmodule K ℂ n :=
  (Finsupp.basisSingleOne.symmetricPower n).equiv
    (TauCeti.homogeneousMonomialBasis n) (Sym.equivFinsuppDegree K n)

theorem exponent_ofFn (n : ℕ) (f : Fin n → K) :
    (Sym.equivFinsuppDegree K n (TauCeti.Sym.ofFn f)).val =
      ∑ i, Finsupp.single (f i) 1 := by
  classical
  ext a
  change (TauCeti.Sym.ofFn f : Multiset K).count a = _
  rw [TauCeti.Sym.count_coe_ofFn, Finset.card_filter]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem equiv_basis (n : ℕ) (f : Fin n → K) :
    (equiv n (SymmetricPower.tprod ℂ (fun i => Finsupp.single (f i) 1)) : MvPolynomial K ℂ) =
      ∏ i, X (f i) := by
  classical
  have hb : SymmetricPower.tprod ℂ (fun i => Finsupp.single (f i) 1) =
      Finsupp.basisSingleOne.symmetricPower n (TauCeti.Sym.ofFn f) := by
    simp [Module.Basis.symmetricPower_apply]
  rw [hb, equiv, Module.Basis.equiv_apply, TauCeti.coe_homogeneousMonomialBasis, exponent_ofFn]
  simpa only [Finset.prod_const_one, ← MvPolynomial.X_pow_eq_monomial, pow_one] using
    MvPolynomial.monomial_sum_prod Finset.univ (fun i => Finsupp.single (f i) 1)
      (fun _ => (1 : ℂ))

def productMap (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => K →₀ ℂ) (MvPolynomial K ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) (MvPolynomial K ℂ)).compLinearMap (fun _ => linearForm)

theorem equiv_pure (n : ℕ) (v : Fin n → K →₀ ℂ) :
    (equiv n (SymmetricPower.tprod ℂ v) : MvPolynomial K ℂ) = ∏ i, linearForm (v i) := by
  have he : ((homogeneousSubmodule K ℂ n).subtype.comp (equiv n).toLinearMap).compMultilinearMap
      (SymmetricPower.tprod ℂ) = productMap n := by
    apply Module.Basis.ext_multilinear (fun _ => Finsupp.basisSingleOne)
    intro f
    simpa [productMap, linearForm] using equiv_basis n f
  exact MultilinearMap.congr_fun he v

end
end Math.SymmetricPolynomialPower
