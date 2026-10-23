import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Math.RepresentationTheory.Unitary.FourDoubletProductExchange

open Math

/-! Four weak doublets and four left Weyl spinors: the four product contractions
exhaust invariants of the independent weak and Lorentz groups. -/
namespace Physics.FourWeakWeylCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor FourDoubletInvariant
open scoped TensorProduct

def weakRepresentation :=
  ((SmallSpecialUnitary.defining 2).tprod (SmallSpecialUnitary.defining 2)).tprod
    ((SmallSpecialUnitary.defining 2).tprod (SmallSpecialUnitary.defining 2))

def weakPairing (i : Fin 2) : IntertwiningMap weakRepresentation
    (Representation.trivial ℂ FourDoubletInvariant.Group ℂ) where
  toLinearMap := tensorPairing (i = 1)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    apply TensorProduct.ext
    apply LinearMap.ext; intro c
    apply LinearMap.ext; intro d
    exact tensorPairing_invariant (i = 1) g a b c d

theorem weak_formula (f : IntertwiningMap weakRepresentation
    (Representation.trivial ℂ FourDoubletInvariant.Group ℂ)) :
    f = ∑ i, f (FourSameWeylCompleteness.probe i) • weakPairing i := by
  apply IntertwiningMap.ext
  have hf : IsInvariant f.toLinearMap := by
    intro g a b c d
    exact IntertwiningMap.isIntertwining _ _ f g ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
  simpa [Fin.sum_univ_two, weakPairing, FourSameWeylCompleteness.probe, value] using
    formula f.toLinearMap hf

theorem weak_probe (i j : Fin 2) :
    weakPairing i (FourSameWeylCompleteness.probe j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [weakPairing, FourSameWeylCompleteness.probe, tensorPairing_apply, eps, basis]

def representation := external weakRepresentation (FourSameWeylCompleteness.representation false)
abbrev Coefficient := IntertwiningMap representation
  (Representation.trivial ℂ (FourDoubletInvariant.Group × WeylSpinor.Group) ℂ)

def pairing (ij : Fin 2 × Fin 2) := coefficient (weakPairing ij.1)
  (FourSameWeylCompleteness.basisPairing false ij.2)
def probe (ij : Fin 2 × Fin 2) :=
  FourSameWeylCompleteness.probe ij.1 ⊗ₜ[ℂ] FourSameWeylCompleteness.probe ij.2

theorem pairing_probe (ij kl : Fin 2 × Fin 2) :
    pairing ij (probe kl) = if ij = kl then 1 else 0 := by
  change weakPairing ij.1 (FourSameWeylCompleteness.probe kl.1) *
    FourSameWeylCompleteness.basisPairing false ij.2 (FourSameWeylCompleteness.probe kl.2) = _
  rw [weak_probe, FourSameWeylCompleteness.basisPairing_probe]
  by_cases h1 : ij.1 = kl.1 <;> by_cases h2 : ij.2 = kl.2 <;> simp [Prod.ext_iff, h1, h2]

theorem reconstruction (f : Coefficient) : f = ∑ ij, f (probe ij) • pairing ij :=
  FiniteInvariantFactor.product_formula _ _ _ _ weak_formula _ _
    (FourSameWeylCompleteness.basisPairing_formula false) f

/-- Local classification with explicit four probes and contraction inverse. -/
def coordinates : Coefficient ≃ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun f ij := f (probe ij)
  invFun k := ∑ ij, k ij • pairing ij
  left_inv f := (reconstruction f).symm
  right_inv k := by
    funext ij
    change (∑ kl, k kl • pairing kl) (probe ij) = k ij
    rw [IntertwiningMap.sum_apply]
    change (∑ kl, k kl * pairing kl (probe ij)) = k ij
    simp [pairing_probe]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Physics.FourWeakWeylCompleteness
