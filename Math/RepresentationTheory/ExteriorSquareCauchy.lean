import Math.LinearAlgebra.ExteriorSquareCauchy
import Math.RepresentationTheory.ExternalInvariantTensor

/-! Equivariant, complete exterior-square Cauchy decomposition with arbitrary
retained group actions. The inverse is the proved basis-free linear inverse. -/
namespace Math.ExteriorSquareCauchyRepresentation
set_option autoImplicit false
noncomputable section
open Representation TensorSquareQuotients
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

variable {G A B : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)

@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.First (A := A) (B := B)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Second (A := A) (B := B)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Total (A := A) (B := B)) := inferInstance

abbrev firstAction := (a.exteriorPower 2).tprod (b.symmetricPower 2)
abbrev secondAction := (a.symmetricPower 2).tprod (b.exteriorPower 2)

theorem wedge_natural (f : A →ₗ[ℂ] A) (x y : A) :
    wedge (f x ⊗ₜ[ℂ] f y)=exteriorPower.map 2 f (wedge (x ⊗ₜ[ℂ] y)) := by
  rw [ExteriorSquareTensorDescent.wedge_tmul,ExteriorSquareTensorDescent.wedge_tmul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem sym_natural (f : A →ₗ[ℂ] A) (x y : A) :
    sym (f x ⊗ₜ[ℂ] f y)=SymmetricPower.map (ι := Fin 2) f (sym (x ⊗ₜ[ℂ] y)) := by
  rw [sym_tmul,sym_tmul,SymmetricPower.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

private theorem raw_first_natural (g : G) :
    (ExteriorSquareCauchy.rawFirst (A := A) (B := B)).comp (((a.tprod b).tprod (a.tprod b)) g)=
      (firstAction a b g).comp ExteriorSquareCauchy.rawFirst := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply TensorProduct.ext
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro w
  change wedge (a g x ⊗ₜ[ℂ] a g z) ⊗ₜ[ℂ] sym (b g y ⊗ₜ[ℂ] b g w)=
    (a.exteriorPower 2) g (wedge (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ]
      (b.symmetricPower 2) g (sym (y ⊗ₜ[ℂ] w))
  exact congrArg₂ (fun u v => u ⊗ₜ[ℂ] v) (wedge_natural (a g) x z) (sym_natural (b g) y w)

private theorem raw_second_natural (g : G) :
    (ExteriorSquareCauchy.rawSecond (A := A) (B := B)).comp (((a.tprod b).tprod (a.tprod b)) g)=
      (secondAction a b g).comp ExteriorSquareCauchy.rawSecond := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply TensorProduct.ext
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro w
  change sym (a g x ⊗ₜ[ℂ] a g z) ⊗ₜ[ℂ] wedge (b g y ⊗ₜ[ℂ] b g w)=
    (a.symmetricPower 2) g (sym (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ]
      (b.exteriorPower 2) g (wedge (y ⊗ₜ[ℂ] w))
  exact congrArg₂ (fun u v => u ⊗ₜ[ℂ] v) (sym_natural (a g) x z) (wedge_natural (b g) y w)

def first : IntertwiningMap ((a.tprod b).exteriorPower 2) (firstAction a b) where
  toLinearMap := ExteriorSquareCauchy.first
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change ExteriorSquareCauchy.first (((a.tprod b).exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v))=
      firstAction a b g (ExteriorSquareCauchy.first (exteriorPower.ιMulti ℂ 2 v))
    rw [Representation.exteriorPower_apply_ιMulti,← wedge_eta,← wedge_eta,
      ExteriorSquareCauchy.first_wedge,ExteriorSquareCauchy.first_wedge]
    exact LinearMap.congr_fun (raw_first_natural a b g) (v 0 ⊗ₜ[ℂ] v 1)

def second : IntertwiningMap ((a.tprod b).exteriorPower 2) (secondAction a b) where
  toLinearMap := ExteriorSquareCauchy.second
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change ExteriorSquareCauchy.second (((a.tprod b).exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v))=
      secondAction a b g (ExteriorSquareCauchy.second (exteriorPower.ιMulti ℂ 2 v))
    rw [Representation.exteriorPower_apply_ιMulti,← wedge_eta,← wedge_eta,
      ExteriorSquareCauchy.second_wedge,ExteriorSquareCauchy.second_wedge]
    exact LinearMap.congr_fun (raw_second_natural a b g) (v 0 ⊗ₜ[ℂ] v 1)

def equivalence : Representation.Equiv ((a.tprod b).exteriorPower 2)
    ((firstAction a b).prod (secondAction a b)) where
  toLinearEquiv := ExteriorSquareCauchy.equivalence
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (first a b).isIntertwining _ _ g x
    · exact (second a b).isIntertwining _ _ g x

end
end Math.ExteriorSquareCauchyRepresentation
