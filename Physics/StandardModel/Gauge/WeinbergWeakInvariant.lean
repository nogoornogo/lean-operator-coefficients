import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Math.RepresentationTheory.TwoComponentSymmetricSquare

open Math

/-! The weak invariant line for two lepton doublets and a symmetric Higgs pair.
Completeness is transported from the exhaustive triplet contraction, not assumed. -/
namespace GUT.WeinbergWeakInvariant
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentContractions
open DipoleGaugeTensor SMEpsilonTensor
open scoped TensorProduct

def higgsDualEquiv : Representation.Equiv (weak.symmetricPower 2) adjoint.dual where
  toLinearEquiv := (TwoComponentSymmetricSquare.equiv.trans
    TwoComponentTripletDual.equiv).toLinearEquiv
  isIntertwining' g := by
    apply SymmetricSquareDescent.ext
    intro h
    have he := IntertwiningMap.isIntertwining _ _
      (TwoComponentSymmetricSquare.equiv.trans
        TwoComponentTripletDual.equiv).toIntertwiningMap (weakToSL g)
      (SymmetricPower.tprod ℂ h)
    simpa [Representation.symmetricPower_apply_tprod, weak, adjoint,
      Representation.dual_apply, MonoidHom.comp_apply] using he

def domain := (weak.tprod weak).tprod (weak.symmetricPower 2)

def domainEquiv : Representation.Equiv domain tripletRepresentation :=
  ExternalInvariantTensor.tensorEquiv (Representation.Equiv.refl _) higgsDualEquiv

abbrev Coefficient := IntertwiningMap domain (Representation.trivial ℂ WeakGroup ℂ)

def contraction : Coefficient := tripletContraction.comp domainEquiv.toIntertwiningMap

def witness := (weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ]
  SymmetricPower.tprod ℂ ![weakBasis 1, weakBasis 1]

theorem contraction_apply (x y : Weak) (h : Fin 2 → Weak) :
    contraction ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SymmetricPower.tprod ℂ h) =
      (eps2 x (h 0) * eps2 y (h 1) + eps2 x (h 1) * eps2 y (h 0)) / 2 := by
  change TwoComponentTripletDual.metric
    (TwoComponentSymmetricSquare.equiv.toLinearEquiv (SymmetricPower.tprod ℂ h))
    (pair (x ⊗ₜ[ℂ] y)) = _
  change TwoComponentTripletDual.metric
    (TwoComponentSymmetricSquare.descend (SymmetricPower.tprod ℂ h))
    (pair (x ⊗ₜ[ℂ] y)) = _
  rw [TwoComponentSymmetricSquare.descend_tprod, pair_tmul, pair_tmul]
  simp [TwoComponentTripletDual.metric, eps2]
  ring

@[simp] theorem contraction_witness : contraction witness = 1 := by
  rw [witness, contraction_apply]
  norm_num [eps2, weakBasis]

theorem unique (f : Coefficient) : f = f witness • contraction := by
  let k := f.comp domainEquiv.symm.toIntertwiningMap
  have hk := DipoleGaugeTensor.triplet_unique k
  have hf : f = k tripletWitness • contraction := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun t => t (domainEquiv.toLinearEquiv x)) hk
    change f (domainEquiv.toLinearEquiv.symm (domainEquiv.toLinearEquiv x)) =
      k tripletWitness • contraction x at h
    rw [domainEquiv.toLinearEquiv.symm_apply_apply] at h
    exact h
  have he : f witness = k tripletWitness := by rw [hf]; simp
  rw [he]
  exact hf

def coordinateEquiv : Coefficient ≃ₗ[ℂ] ℂ where
  toFun f := f witness
  invFun z := z • contraction
  left_inv f := (unique f).symm
  right_inv z := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equal Higgs arguments remove the polarization factor. -/
theorem diagonal_apply (x y h : Weak) :
    contraction ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SymmetricPower.tprod ℂ ![h,h]) =
      eps2 x h * eps2 y h := by
  rw [contraction_apply]
  simp

end
end GUT.WeinbergWeakInvariant
