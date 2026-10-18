import Math.RepresentationTheory.GenerationExteriorExhaustion
import Math.RepresentationTheory.TopExteriorCauchy
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.LinearAlgebra.SelectionCriteria

/-! Equivariant projection onto one generation, surjective in every exterior
degree. It lifts nonzero coefficients without extending by a chosen complement. -/
namespace Math.GenerationExteriorProjection
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (r : Representation ℂ G V) (s : Representation ℂ G W)

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

def project : IntertwiningMap (GenerationExteriorExhaustion.generations r) r where
  toLinearMap := TopExteriorCauchy.evaluate (LinearMap.proj (0 : Fin 3))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x f
    change f 0 • r g x=r g (f 0 • x)
    exact (map_smul _ _ _).symm

theorem project_surjective : Function.Surjective (project r) := by
  intro x
  refine ⟨x ⊗ₜ[ℂ] Pi.single (0 : Fin 3) (1 : ℂ),?_⟩
  simp [project,TopExteriorCauchy.evaluate_tmul]

theorem exterior_surjective (n : ℕ) : Function.Surjective ((project r).exteriorPower n) :=
  exteriorPower.map_surjective (n := n) (project_surjective r)

theorem tensor_allowed (n m : ℕ)
    (h : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((r.exteriorPower n).tprod (s.exteriorPower m)))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (((GenerationExteriorExhaustion.generations r).exteriorPower n).tprod
        ((GenerationExteriorExhaustion.generations s).exteriorPower m))) := by
  obtain ⟨f,hf⟩ := h
  let p := ((project r).exteriorPower n).tensor ((project s).exteriorPower m)
  have hp : Function.Surjective p := TensorProduct.map_surjective
    (exterior_surjective r n) (exterior_surjective s m)
  refine ⟨f.comp p,?_⟩
  intro hz
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := hp y
  exact DFunLike.congr_fun hz x

end
end Math.GenerationExteriorProjection
