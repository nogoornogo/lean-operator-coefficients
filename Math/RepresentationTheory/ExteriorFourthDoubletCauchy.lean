import Math.LinearAlgebra.ExteriorFourthDoubletCauchy
import Math.LinearAlgebra.ExteriorFourthDoubletNaturality
import Math.RepresentationTheory.ExteriorFourthKernels
import Math.RepresentationTheory.ExteriorFourthColumn
import Math.RepresentationTheory.ExteriorCubeDoublet
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums

/-! The complete quartic doublet Cauchy equivalence retains every factor
of an arbitrary group action on A. No branching premise is supplied. -/
namespace Math.ExteriorFourthDoubletCauchyRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A) (j : G →* WeakDoubletScalars.Group)
abbrev spin := ExteriorCubeDoubletRepresentation.spin j
abbrev total := (r.tprod (spin j)).exteriorPower 4
abbrev top := (r.exteriorPower 4).tprod ((spin j).symmetricPower 4)
abbrev middle := (ExteriorFourthKernelsRepresentation.action211 r).tprod ((spin j).symmetricPower 2)
abbrev last := ExteriorFourthKernelsRepresentation.action22 r
abbrev source13 := (ExteriorFourthKernelsRepresentation.source13 r).tprod ((spin j).symmetricPower 2)
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorFourthDoublet.Target13 (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup
    (ExteriorFourthKernels.K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 ExteriorFourthDoublet.B) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorFourthDoubletCauchy.Domain (A := A)) := inferInstance

def insert13 : IntertwiningMap (source13 r j) (total r j) where
  toLinearMap := ExteriorFourthDoublet.insert13
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthDoubletNaturality.insert13_natural (r g) (spin j g)
      (ExteriorCubeDoublet.spinVolume_invariant _
        (ExteriorCubeDoubletRepresentation.spin_determinant j g)) x

def insert211 : IntertwiningMap (middle r j) (total r j) :=
  (insert13 r j).comp ((ExteriorFourthKernelsRepresentation.kernel211 r).subtype.tensor
    (IntertwiningMap.id ((spin j).symmetricPower 2)))

def insert22 : IntertwiningMap (ExteriorFourthKernelsRepresentation.source22 r) (total r j) where
  toLinearMap := ExteriorFourthDoublet22.insert22
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthDoubletNaturality.insert22_natural (r g) (spin j g)
      (ExteriorCubeDoublet.spinVolume_invariant _
        (ExteriorCubeDoubletRepresentation.spin_determinant j g)) x

def insertK22 : IntertwiningMap (last r) (total r j) :=
  (insert22 r j).comp (ExteriorFourthKernelsRepresentation.kernel22 r).subtype

theorem insert211_injective : Function.Injective (insert211 r j) :=
  ExteriorFourthDoublet.insert211_injective (A := A)

theorem insertK22_injective : Function.Injective (insertK22 r j) :=
  ExteriorFourthDoublet22.insertK22_injective (A := A)

def column : IntertwiningMap (top r j) (total r j) :=
  ExteriorFourthColumnRepresentation.column r (spin j)

def combine : IntertwiningMap ((top r j).prod ((middle r j).prod (last r))) (total r j) :=
  (column r j).comp (IntertwiningMap.fst ℂ _ _)+
    (insert211 r j).comp ((IntertwiningMap.fst ℂ _ _).comp (IntertwiningMap.snd ℂ _ _))+
    (insertK22 r j).comp ((IntertwiningMap.snd ℂ _ _).comp (IntertwiningMap.snd ℂ _ _))

/-- The three actual quartic constituents, with a complete equivariant
inverse, for any finite-dimensional A and pulled-back SU2 doublet. -/
def equivalence [FiniteDimensional ℂ A] :
    Representation.Equiv ((top r j).prod ((middle r j).prod (last r))) (total r j) where
  toLinearEquiv := ExteriorFourthDoubletCauchy.equivalence
  isIntertwining' := (combine r j).isIntertwining'

def complement : IntertwiningMap ((middle r j).prod (last r))
    (ExteriorFourthColumnRepresentation.action r (spin j)) :=
  (ExteriorFourthColumnRepresentation.project r (spin j)).comp
    ((insert211 r j).comp (IntertwiningMap.fst ℂ _ _)+
      (insertK22 r j).comp (IntertwiningMap.snd ℂ _ _))

/-- Cancel the actual finite top column from the two proved equivariant
splits. The linear projected insertion/extraction is proved separately. -/
def complementEquivalence [FiniteDimensional ℂ A] :
    Representation.Equiv ((middle r j).prod (last r))
      (ExteriorFourthColumnRepresentation.action r (spin j)) := by
  let e : Representation.Equiv
      ((ExteriorFourthColumnRepresentation.action r (spin j)).prod (top r j))
      (((middle r j).prod (last r)).prod (top r j)) :=
    (TensorProductSums.prodComm _ _).trans
      ((ExteriorFourthColumnRepresentation.split r (spin j)).symm.trans
        ((equivalence r j).symm.trans (TensorProductSums.prodComm _ _)))
  exact (Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := (ExteriorFourthColumnRepresentation.kernel r (spin j)).toSubmodule)
    (B := ExteriorFourthDoubletCauchy.Tail (A := A))
    (C := ExteriorFourthColumn.Column (A := A) (B := ExteriorFourthDoublet.B))
    (ExteriorFourthColumnRepresentation.action r (spin j))
    ((middle r j).prod (last r)) (top r j) e)).symm

end
end Math.ExteriorFourthDoubletCauchyRepresentation
