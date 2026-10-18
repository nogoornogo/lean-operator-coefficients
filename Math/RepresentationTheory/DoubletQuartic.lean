import Math.RepresentationTheory.SymmetricFourth22
import Math.RepresentationTheory.ScalarSymmetricSquare
import Math.RepresentationTheory.SymmetricExteriorSquare
import Math.RepresentationTheory.DoubletCubicHook
import Math.RepresentationTheory.SU2ClebschGordan
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums
import Math.LinearAlgebra.SymmetricPowerLowDegree

/-! The weak factors needed for actual Q quartic resolution. All factors
follow from universal shuffle splits and the proved SU2 tensor equivalence;
the spin-one exterior square is obtained by finite summand cancellation. -/
namespace Math.DoubletQuartic
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G : Type*} [Group G] (j : G →* WeakDoubletScalars.Group)
abbrev B := WeakDoubletScalars.Doublet
abbrev spin := DoubletCubicHook.spin j
abbrev scalar := trivial ℂ G ℂ

def kernel22 : Representation.Equiv (ExteriorFourthKernelsRepresentation.action22 (spin j))
    (scalar (G := G)) :=
  (SymmetricFourth22Representation.kernelFull (spin j) (by simp [WeakDoubletScalars.Doublet])).trans
    (((DoubletCubicHook.top2 j).symmetricPower 2).trans (ScalarSymmetricSquare.equivalence G))

def symmetricSpinOne : Representation.Equiv (((spin j).symmetricPower 2).symmetricPower 2)
    (((spin j).symmetricPower 4).prod (scalar (G := G))) :=
  (SymmetricFourth22Representation.equivalence (spin j)).trans (prodEquiv (.refl _) (kernel22 j))

def tensorSquare : Representation.Equiv ((spin j).tprod (spin j))
    (((spin j).symmetricPower 2).prod (scalar (G := G))) :=
  (SymmetricExteriorSquare.equivalence (spin j)).trans
    (prodEquiv (.refl _) (DoubletCubicHook.top2 j))

private def twoBlocks {K : Type*} [Group K] {A : Fin 2 → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (r : ∀ i, Representation ℂ K (A i)) : Representation.Equiv
      (FiniteBlockHom.action r) ((r 0).prod (r 1)) where
  toLinearEquiv := LinearEquiv.piFinTwo ℂ A
  isIntertwining' _ := by ext x <;> rfl

private def threeBlocks {K : Type*} [Group K] {A : Fin 3 → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (r : ∀ i, Representation ℂ K (A i)) : Representation.Equiv
      (FiniteBlockHom.action r) ((r 0).prod ((r 1).prod (r 2))) where
  toLinearEquiv := (Fin.consLinearEquiv ℂ A).symm.trans
    (LinearEquiv.prodCongr (.refl ℂ _) (LinearEquiv.piFinTwo ℂ (fun i => A i.succ)))
  isIntertwining' _ := by ext x <;> rfl

private def cg13 : Representation.Equiv
    (WeakDoubletScalars.doublet.tprod (WeakDoubletScalars.doublet.symmetricPower 3))
    ((WeakDoubletScalars.doublet.symmetricPower 4).prod (WeakDoubletScalars.doublet.symmetricPower 2)) :=
  (tensorEquiv (SymmetricPowerLowDegree.representationOneEquiv WeakDoubletScalars.doublet).symm
    (.refl _)).trans ((SU2ClebschGordan.equivalence 1 3).symm.trans
      (twoBlocks (SU2ClebschGordan.summand 1 3)))

def tensorCube : Representation.Equiv ((spin j).tprod ((spin j).symmetricPower 3))
    (((spin j).symmetricPower 4).prod ((spin j).symmetricPower 2)) := restrictEquiv cg13 j

private def cg22 : Representation.Equiv
    ((WeakDoubletScalars.doublet.symmetricPower 2).tprod (WeakDoubletScalars.doublet.symmetricPower 2))
    ((WeakDoubletScalars.doublet.symmetricPower 4).prod
      ((WeakDoubletScalars.doublet.symmetricPower 2).prod (trivial ℂ WeakDoubletScalars.Group ℂ))) :=
  (SU2ClebschGordan.equivalence 2 2).symm.trans
    ((threeBlocks (SU2ClebschGordan.summand 2 2)).trans
      (prodEquiv (.refl _)
        (prodEquiv (.refl _) (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet))))

abbrev common := ((spin j).symmetricPower 4).prod (scalar (G := G))

def sourceSymmetric : Representation.Equiv
    (((spin j).symmetricPower 2).tprod ((spin j).symmetricPower 2))
    ((((spin j).symmetricPower 2).exteriorPower 2).prod (common j)) :=
  (SymmetricExteriorSquare.equivalence ((spin j).symmetricPower 2)).trans
    ((prodEquiv (symmetricSpinOne j) (.refl _)).trans (TensorProductSums.prodComm _ _))

def reorder : Representation.Equiv
    (((spin j).symmetricPower 4).prod (((spin j).symmetricPower 2).prod (scalar (G := G))))
    (((spin j).symmetricPower 2).prod (common j)) where
  toLinearEquiv :=
    { toFun x := (x.2.1,(x.1,x.2.2))
      invFun x := (x.2.1,(x.1,x.2.2))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

/-- The spin-one exterior square is spin one, derived without a new
character/multiplicity calculation or a determinant premise. -/
def exteriorSpinOne : Representation.Equiv (((spin j).symmetricPower 2).exteriorPower 2)
    ((spin j).symmetricPower 2) :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := ⋀[ℂ]^2 (Sym[ℂ]^2 B)) (B := Sym[ℂ]^2 B)
    (C := (Sym[ℂ]^4 B) × ℂ)
    (((spin j).symmetricPower 2).exteriorPower 2) ((spin j).symmetricPower 2) (common j)
    ((sourceSymmetric j).symm.trans ((restrictEquiv cg22 j).trans (reorder j))))

end
end Math.DoubletQuartic
