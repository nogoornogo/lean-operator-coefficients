import Math.RepresentationTheory.Multiplicity.FiniteSpectrum
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

namespace Math.CopySumEquivalence
set_option autoImplicit false
noncomputable section
open Representation FiniteSpectrum
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def copiesAdd (n m : ℕ) (r : Representation ℂ G V) :
    Representation.Equiv (copies (n+m) r) ((copies n r).prod (copies m r)) where
  toLinearEquiv :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (n+m) => V)
      (finSumFinEquiv.symm : Fin (n+m) ≃ Fin n ⊕ Fin m)).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℂ V)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> funext i <;> rfl

def copiesProd (n : ℕ) (r : Representation ℂ G V) (s : Representation ℂ G W) :
    Representation.Equiv ((copies n r).prod (copies n s)) (copies n (r.prod s)) where
  toLinearEquiv :=
    { toFun := fun x i => (x.1 i,x.2 i)
      invFun := fun x => (fun i => (x i).1,fun i => (x i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

def assoc (r : Representation ℂ G V) (s : Representation ℂ G W)
    {U : Type*} [AddCommGroup U] [Module ℂ U] (t : Representation ℂ G U) :
    Representation.Equiv ((r.prod s).prod t) (r.prod (s.prod t)) where
  toLinearEquiv := LinearEquiv.prodAssoc ℂ V W U
  isIntertwining' _ := rfl
end
end Math.CopySumEquivalence
