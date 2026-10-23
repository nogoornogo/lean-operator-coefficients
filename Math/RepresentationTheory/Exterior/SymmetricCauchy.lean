import Math.LinearAlgebra.Constructions.PairedMultilinear
import Math.LinearAlgebra.Symmetric.SymmetricPurePowers
import Math.RepresentationTheory.Symmetric.SymmetricMultilinearDiagonal

/-! The row component of Cauchy, constructed by symmetrizing both sets of slots. -/
namespace Math.SymmetricCauchy
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def right (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => A)
    (Sym[ℂ]^n B →ₗ[ℂ] Sym[ℂ]^n (A ⊗[ℂ] B)) :=
  (SymmetricPowerDescent.equiv (A := B) (N := Sym[ℂ]^n (A ⊗[ℂ] B)) n).symm.toLinearMap.compMultilinearMap
    ((SymmetricMultilinearProjection.project n).compMultilinearMap
      (PairedMultilinear.map (SymmetricPower.tprod ℂ)))

def map (n : ℕ) : Sym[ℂ]^n A ⊗[ℂ] Sym[ℂ]^n B →ₗ[ℂ]
    Sym[ℂ]^n (A ⊗[ℂ] B) :=
  TensorProduct.lift (SymmetricPowerDescent.lift (A := A)
    (N := Sym[ℂ]^n B →ₗ[ℂ] Sym[ℂ]^n (A ⊗[ℂ] B)) n
    (SymmetricMultilinearProjection.project (B := A)
      (N := Sym[ℂ]^n B →ₗ[ℂ] Sym[ℂ]^n (A ⊗[ℂ] B)) n (right n)))

theorem diagonal (n : ℕ) (a : A) (b : B) :
    map n (SymmetricPower.tprod ℂ (fun _ : Fin n => a) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin n => b)) =
      SymmetricPower.tprod ℂ (fun _ : Fin n => a ⊗ₜ[ℂ] b) := by
  change (SymmetricPowerDescent.lift (A := A)
    (N := Sym[ℂ]^n B →ₗ[ℂ] Sym[ℂ]^n (A ⊗[ℂ] B)) n
    (SymmetricMultilinearProjection.project (B := A)
      (N := Sym[ℂ]^n B →ₗ[ℂ] Sym[ℂ]^n (A ⊗[ℂ] B)) n (right n))
      (SymmetricPower.tprod ℂ (fun _ : Fin n => a)))
        (SymmetricPower.tprod ℂ (fun _ : Fin n => b)) = _
  rw [SymmetricMultilinearProjection.lift_project_diagonal]
  change SymmetricPowerDescent.lift n
    (SymmetricMultilinearProjection.project n
      (PairedMultilinear.map (SymmetricPower.tprod ℂ) (fun _ : Fin n => a)))
        (SymmetricPower.tprod ℂ (fun _ : Fin n => b)) = _
  rw [SymmetricMultilinearProjection.lift_project_diagonal]
  rfl

theorem natural (n : ℕ) (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    (SymmetricPower.map (ι := Fin n) (TensorProduct.map f g)).comp (map n) =
      (map n).comp (TensorProduct.map
        (SymmetricPower.map (ι := Fin n) f) (SymmetricPower.map (ι := Fin n) g)) := by
  apply SymmetricPurePowers.tensor_ext
  intro a b
  change SymmetricPower.map (TensorProduct.map f g)
      (map n (SymmetricPower.tprod ℂ (fun _ => a) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ => b))) = _
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, SymmetricPower.map_tprod,
    diagonal, TensorProduct.map_tmul]

variable {G : Type*} [Group G]

def intertwiner (a : Representation ℂ G A) (b : Representation ℂ G B) (n : ℕ) :
    IntertwiningMap ((a.symmetricPower n).tprod (b.symmetricPower n))
      ((a.tprod b).symmetricPower n) where
  toLinearMap := map n
  isIntertwining' g := (natural n (a g) (b g)).symm

end
end Math.SymmetricCauchy
