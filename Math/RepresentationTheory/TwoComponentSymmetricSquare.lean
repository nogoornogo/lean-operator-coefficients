import Math.RepresentationTheory.TwoComponentTensorUniqueness
import Math.RepresentationTheory.TensorSquareMultilinear

/-! Identify the concrete triplet with the independently defined symmetric
square quotient. -/
namespace Math.TwoComponentSymmetricSquare
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentTensorUniqueness
open scoped TensorProduct

def descend : IntertwiningMap (doublet.symmetricPower 2) triplet :=
  TensorSquareMultilinear.symmetricSquareEquiv doublet triplet
    ⟨pair, fun x y => pair_symmetric y x⟩

@[simp] theorem descend_tprod (v : Fin 2 → Doublet) :
    descend (SymmetricPower.tprod ℂ v) = pair (v 0 ⊗ₜ[ℂ] v 1) := by
  simp [descend, TensorSquareMultilinear.symmetricSquareEquiv,
    TensorSquareMultilinear.symmetricEquiv, TensorSquareMultilinear.toEquivariant,
    TensorSquareMultilinear.toMultilinear, SymmetricSquareDescent.equivariantEquiv,
    SymmetricSquareDescent.descend]

def fromTriplet : Triplet →ₗ[ℂ] Sym[ℂ]^2 Doublet where
  toFun z := z 0 • SymmetricPower.tprod ℂ ![basis2 0,basis2 0] +
    (2*z 1) • SymmetricPower.tprod ℂ ![basis2 0,basis2 1] +
    z 2 • SymmetricPower.tprod ℂ ![basis2 1,basis2 1]
  map_add' z w := by simp [mul_add, add_smul]; abel
  map_smul' c z := by simp [smul_add, smul_smul, mul_left_comm]

@[simp] theorem fromTriplet_vector (x y z : ℂ) : fromTriplet ![x,y,z] =
    x • SymmetricPower.tprod ℂ ![basis2 0,basis2 0] +
    (2*y) • SymmetricPower.tprod ℂ ![basis2 0,basis2 1] +
    z • SymmetricPower.tprod ℂ ![basis2 1,basis2 1] := rfl

theorem descend_fromTriplet (z : Triplet) : descend (fromTriplet z) = z := by
  ext i
  fin_cases i <;> simp [fromTriplet, basis2]
  ring

private theorem swap_basis : SymmetricPower.tprod ℂ ![basis2 1,basis2 0] =
    SymmetricPower.tprod ℂ ![basis2 0,basis2 1] := by
  have h := SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap 0 1) ![basis2 0,basis2 1]
  have hv : ![basis2 1,basis2 0] = ![basis2 0,basis2 1] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp
  rw [hv]
  exact h

theorem fromTriplet_pair : fromTriplet.comp pair.toLinearMap =
    TensorSquareMultilinear.fromMultilinear (SymmetricPower.tprod ℂ) := by
  apply ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).ext
  rintro ⟨i,j⟩
  simp only [Module.Basis.tensorProduct_apply, Pi.basisFun_apply]
  change fromTriplet (pair (basis2 i ⊗ₜ[ℂ] basis2 j)) =
    SymmetricPower.tprod ℂ ![basis2 i,basis2 j]
  fin_cases i <;> fin_cases j <;>
    norm_num [pair_tmul, basis2, fromTriplet_vector]
  exact swap_basis.symm

theorem fromTriplet_descend : fromTriplet.comp descend.toLinearMap = LinearMap.id := by
  apply SymmetricSquareDescent.ext
  intro v
  change fromTriplet (descend (SymmetricPower.tprod ℂ v)) = SymmetricPower.tprod ℂ v
  rw [descend_tprod]
  exact LinearMap.congr_fun fromTriplet_pair (v 0 ⊗ₜ[ℂ] v 1) |>.trans (by
    change SymmetricPower.tprod ℂ ![v 0,v 1] = SymmetricPower.tprod ℂ v
    congr 1
    ext i
    fin_cases i <;> rfl)

def equiv : Representation.Equiv (doublet.symmetricPower 2) triplet where
  toLinearEquiv := {
    toLinearMap := descend.toLinearMap
    invFun := fromTriplet
    left_inv z := LinearMap.congr_fun fromTriplet_descend z
    right_inv := descend_fromTriplet }
  isIntertwining' := descend.isIntertwining'

end
end Math.TwoComponentSymmetricSquare
