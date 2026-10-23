import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Exterior.ComplementaryExteriorDuality
import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Math.RepresentationTheory.Decomposition.IrreducibilityTransport
import Math.RepresentationTheory.Characters.CompactCoefficientSupport
import Math.RepresentationTheory.Decomposition.ProductFactorization
import Math.RepresentationTheory.Decomposition.Schur

/-! Actual defining SU3 exterior branches, with determinant-one volume and
the degree-two contragredient identified. No highest-weight classification
or color tensor-product rule is assumed. -/
namespace Math.SU3DefiningExterior
set_option autoImplicit false
noncomputable section
open Representation

abbrev Group := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev Vector := Fin 3 → ℂ
abbrev rho := SmallSpecialUnitary.defining 3
def basis := Pi.basisFun ℂ (Fin 3)

theorem dimension : Module.finrank ℂ Vector=3 := by simp [Vector]

theorem determinant (g : Group) : LinearMap.det (rho g)=1 := by
  change LinearMap.det (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.prop.2

def volume := Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ Vector)

def twoEquiv : Representation.Equiv (rho.exteriorPower 2) rho.dual :=
  (ComplementaryExteriorDuality.equiv rho determinant volume (by rw [dimension])).trans
    (SplitRepresentationProjection.dualEquiv rho.exteriorPowerOneEquiv)

def topEquiv : Representation.Equiv (rho.exteriorPower 3) (trivial ℂ Group ℂ) where
  toLinearEquiv := Module.Basis.exteriorPowerTopEquiv basis
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change Module.Basis.exteriorPowerTopEquiv basis (exteriorPower.map 3 (rho g) x)=Module.Basis.exteriorPowerTopEquiv basis x
    rw [Module.Basis.map_exteriorPower_top_eq_det_smul basis,determinant g,one_smul]
    rfl

instance definingIrreducible : IsIrreducible rho := SmallSpecialUnitary.defining_three_irreducible

instance dualIrreducible : IsIrreducible rho.dual := RepresentationTheory.dual_isIrreducible rho

instance twoIrreducible : IsIrreducible (rho.exteriorPower 2) :=
  ProductFactorization.isIrreducible_of_equiv twoEquiv

theorem high_zero (n : ℕ) (hn : 3<n) (x : ⋀[ℂ]^n Vector) : x=0 :=
  exteriorPower.eq_zero_of_finrank_lt n (by rw [dimension]; exact hn) x

theorem scalar_iff (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (rho.exteriorPower n)) ↔ n=0 ∨ n=3 := by
  by_cases hn : n≤3
  · interval_cases n
    · simp only [true_or,iff_true]
      refine ⟨rho.exteriorPowerZeroEquiv.toIntertwiningMap,?_⟩
      intro hz
      have he := DFunLike.congr_fun hz (rho.exteriorPowerZeroEquiv.symm 1)
      simp at he
    · simp only [Nat.one_ne_zero,or_false,show (1 : ℕ)≠3 by omega,iff_false]
      rintro ⟨f,hf⟩
      apply hf
      have e := CompactCoefficientSupport.homEquiv rho.exteriorPowerOneEquiv (.refl (trivial ℂ Group ℂ))
      apply e.injective
      rw [map_zero]
      apply BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
      simp
    · simp only [show (2 : ℕ)≠0 by omega,show (2 : ℕ)≠3 by omega,false_or,iff_false]
      rintro ⟨f,hf⟩
      apply hf
      apply BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
      rw [twoEquiv.finrank_eq,Subspace.dual_finrank_eq,dimension]
      simp
    · simp only [or_true,iff_true]
      refine ⟨topEquiv.toIntertwiningMap,?_⟩
      intro hz
      have he := DFunLike.congr_fun hz (topEquiv.symm 1)
      simp at he
  · constructor
    · rintro ⟨f,hf⟩
      apply False.elim
      apply hf
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rw [high_zero n (by omega) x,map_zero]
      rfl
    · intro h
      omega

end
end Math.SU3DefiningExterior
