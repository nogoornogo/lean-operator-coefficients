import Math.LinearAlgebra.Exterior.ExteriorFourthColumn
import Math.RepresentationTheory.Exterior.ExteriorFourthKernels

/-! The actual quartic top column and its complementary kernel, retaining
arbitrary group actions. This is not the complete three-branch Cauchy rule. -/
namespace Math.ExteriorFourthColumnRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G A B : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)
@[reducible] local instance : AddCommGroup (ExteriorFourthColumn.Column (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

abbrev source := (a.exteriorPower 4).tprod (b.symmetricPower 4)
abbrev total := (a.tprod b).exteriorPower 4

def column : IntertwiningMap (source a b) (total a b) where
  toLinearMap := ExteriorSymmetricColumn.column 4
  isIntertwining' g := (ExteriorSymmetricColumn.natural 4 (a g) (b g)).symm

def retract : IntertwiningMap (total a b) (source a b) where
  toLinearMap := ExteriorFourthColumn.retract
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthColumn.retract_natural (a g) (b g) x

theorem retract_column (x : ExteriorFourthColumn.Column (A := A) (B := B)) :
    retract a b (column a b x)=x := ExteriorFourthColumn.retract_column x

theorem column_injective : Function.Injective (column a b) :=
  ExteriorFourthColumn.column_injective

abbrev kernel := (retract a b).ker
abbrev action := (kernel a b).toRepresentation

def remainder : IntertwiningMap (total a b) (total a b) :=
  IntertwiningMap.id _-(column a b).comp (retract a b)

def project : IntertwiningMap (total a b) (action a b) where
  toLinearMap := ExteriorFourthColumn.project
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder a b).isIntertwining _ _ g x

def split : Representation.Equiv (total a b) ((source a b).prod (action a b)) where
  toLinearEquiv := ExteriorFourthColumn.split
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (retract a b).isIntertwining _ _ g x
    · exact (project a b).isIntertwining _ _ g x

end
end Math.ExteriorFourthColumnRepresentation
