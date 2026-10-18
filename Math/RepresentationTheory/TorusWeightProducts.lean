import Math.RepresentationTheory.TorusWeightSlice
import Math.RepresentationTheory.Decomposition.FiniteBlockHom

/-! Actual torus-weight spaces commute with complete product decompositions,
including dependent carriers and all retained commuting group actions. -/
namespace Math.TorusWeightProducts
set_option autoImplicit false
noncomputable section
open Representation TorusWeightSlice
variable {G K I : Type*} [Group G] [Group K]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (r : ∀ i, Representation ℂ (G × K) (V i)) (t : Circle →* G) (n : ℤ)

def equivalence : Representation.Equiv (action (FiniteBlockHom.action r) t n)
    (FiniteBlockHom.action (fun i => action (r i) t n)) where
  toLinearEquiv :=
    { toFun x i := ⟨x.val i, by
        intro z
        exact congrFun (x.property z) i⟩
      invFun x := ⟨fun i => (x i).val, by
        intro z
        funext i
        exact (x i).property z⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

end
end Math.TorusWeightProducts
