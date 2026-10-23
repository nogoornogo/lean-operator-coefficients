import Math.RepresentationTheory.Symmetric.SymmetricDualPairing
import Math.RepresentationTheory.Decomposition.IrreducibleHomScalar
import TauCeti.RepresentationTheory.SU2.Irreducible

/-! Full scalar coefficient spaces for arbitrary symmetric powers of the
actual SU2 doublet and its algebraic dual. -/
namespace Math.WeakDoubletScalars
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

abbrev Group := TauCeti.SU2
abbrev Doublet := Fin 2 → ℂ
abbrev doublet : Representation ℂ Group Doublet :=
  (TauCeti.stdRep ℂ 2).comp TauCeti.SU2.toGL

theorem symmetricPower_eq (m : ℕ) : doublet.symmetricPower m = TauCeti.SU2.symPower m := by
  apply MonoidHom.ext
  intro g
  apply SymmetricPower.ext
  intro v
  simp only [Representation.symmetricPower_apply_tprod,TauCeti.SU2.symPower_apply_tprod]
  rfl

instance symmetricPower_irreducible (m : ℕ) : IsIrreducible (doublet.symmetricPower m) := by
  rw [symmetricPower_eq]
  exact TauCeti.SU2.isIrreducible_symPower m

def vector : Doublet := Pi.single 0 1
def functional : Module.Dual ℂ Doublet := LinearMap.proj 0

theorem functional_vector : functional vector = 1 := by simp [functional,vector]

def duality (m : ℕ) : Representation.Equiv
    (doublet.symmetricPower m) (doublet.dual.symmetricPower m).dual :=
  SymmetricDualPairing.equiv doublet m vector functional (by rw [functional_vector]; exact one_ne_zero)

abbrev Space (h d : ℕ) := IntertwiningMap
  ((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)) (trivial ℂ Group ℂ)

def homEquiv (h d : ℕ) : Space h d ≃ₗ[ℂ]
    IntertwiningMap (doublet.symmetricPower h) (doublet.symmetricPower d) :=
  (InvariantTensorCurry.equiv _ _).trans (InvariantTensorCurry.postcompose _ _ (duality d).symm)

theorem unbalanced_zero (h d : ℕ) (hd : h≠d) (f : Space h d) : f=0 := by
  apply (homEquiv h d).injective
  rw [map_zero]
  apply BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
  rw [TauCeti.SU2.finrank_symPower,TauCeti.SU2.finrank_symPower]
  omega

def coefficient (m : ℕ) : Space m m := SymmetricDualPairing.coefficient doublet m

def probe (m : ℕ) := SymmetricPower.tprod ℂ (fun _ : Fin m => vector) ⊗ₜ[ℂ]
  SymmetricPower.tprod ℂ (fun _ : Fin m => functional)

theorem normalized (m : ℕ) : coefficient m (probe m) = 1 := by
  rw [coefficient,probe,SymmetricDualPairing.coefficient_diagonal,functional_vector,one_pow]

theorem unique (m : ℕ) (f : Space m m) : f = f (probe m) • coefficient m := by
  obtain ⟨z,hz⟩ := IrreducibleHomScalar.scalar_bridge
    (doublet.symmetricPower m) (doublet.dual.symmetricPower m).dual
      (duality m) (InvariantTensorCurry.equiv _ _ f)
  have hf : f=z • coefficient m := by
    apply (InvariantTensorCurry.equiv _ _).injective
    rw [map_smul]
    exact hz
  have hv : f (probe m) = z := by
    rw [hf]
    change z * coefficient m (probe m) = z
    rw [normalized,mul_one]
  rw [hv]
  exact hf

def balancedEquiv (m : ℕ) : Space m m ≃ₗ[ℂ] ℂ where
  toFun f := f (probe m)
  invFun z := z • coefficient m
  left_inv f := (unique m f).symm
  right_inv z := by change z * coefficient m (probe m) = z; rw [normalized,mul_one]
  map_add' f g := rfl
  map_smul' z f := rfl

end
end Math.WeakDoubletScalars
