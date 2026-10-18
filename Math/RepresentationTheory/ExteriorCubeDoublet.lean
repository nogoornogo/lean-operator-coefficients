import Math.LinearAlgebra.ExteriorCubeDoubletNaturality
import Math.LinearAlgebra.ExteriorCubeDoubletSplit
import Math.RepresentationTheory.ExteriorCubeHook

/-! The cubic doublet split respects the entire retained group action.
The doublet may be pulled back from SU2 along any homomorphism. -/
namespace Math.ExteriorCubeDoubletRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A) (j : G →* WeakDoubletScalars.Group)
abbrev spin : Representation ℂ G WeakDoubletScalars.Doublet := WeakDoubletScalars.doublet.comp j
abbrev total := (r.tprod (spin j)).exteriorPower 3
abbrev middle := (ExteriorCubeHookRepresentation.action r).tprod (spin j)
abbrev source := (ExteriorCubeHookRepresentation.source r).tprod (spin j)
@[reducible] local instance : AddCommGroup (ExteriorCubeDoublet.Target (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] ExteriorCubeDoublet.B) := inferInstance

def contract : IntertwiningMap (total r j) (source r j) where
  toLinearMap := ExteriorCubeDoublet.contract
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorCubeDoublet.contract_natural (r g) (spin j g)
      (SU2DoubletDuality.epsilon_invariant (j g)) x

theorem spin_determinant (g : G) : LinearMap.det (spin j g)=1 := by
  change LinearMap.det (Matrix.toLin' (j g : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact (j g).prop.2

def insert : IntertwiningMap (source r j) (total r j) where
  toLinearMap := ExteriorCubeDoublet.insert
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorCubeDoublet.insert_natural (r g) (spin j g)
      (ExteriorCubeDoublet.spinVolume_invariant _ (spin_determinant j g)) x

def hookInsert : IntertwiningMap (middle r j) (total r j) :=
  (insert r j).comp ((ExteriorCubeHookRepresentation.hook r).subtype.tensor
    (IntertwiningMap.id (spin j)))

def hookRetract : IntertwiningMap (total r j) (middle r j) :=
  (9 : ℂ)⁻¹ • ((ExteriorCubeHookRepresentation.project r).tensor
    (IntertwiningMap.id (spin j))).comp (contract r j)

theorem hook_retract_insert (x : ExteriorCubeHook.Hook (V := A) ⊗[ℂ] ExteriorCubeDoublet.B) :
    hookRetract r j (hookInsert r j x)=x := ExteriorCubeDoublet.hook_retract_insert x

variable (basis : Module.Basis (Fin 3) ℂ A) (hd : ∀ g, LinearMap.det (r g)=1)

def column : IntertwiningMap ((spin j).symmetricPower 3) (total r j) :=
  TopExteriorCauchy.intertwiner basis r (spin j) hd

def combine : IntertwiningMap (((spin j).symmetricPower 3).prod (middle r j)) (total r j) :=
  (column r j basis hd).comp (IntertwiningMap.fst ℂ _ _)+
    (hookInsert r j).comp (IntertwiningMap.snd ℂ _ _)

/-- Complete equivariant branching of the cubic colored doublet. -/
def equivalence : Representation.Equiv (((spin j).symmetricPower 3).prod (middle r j)) (total r j) where
  toLinearEquiv := ExteriorCubeDoubletSplit.equivalence basis
  isIntertwining' := (combine r j basis hd).isIntertwining'

end
end Math.ExteriorCubeDoubletRepresentation
