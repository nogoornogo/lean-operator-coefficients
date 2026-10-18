import Math.RepresentationTheory.DoubletQuartic

/-! The small complete doublet tensor decompositions needed by Q degrees
five and six, obtained from the proved uniform Clebsch-Gordan theorem. -/
namespace Math.DoubletMiddleProducts
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n WeakDoubletScalars.Doublet) := Module.addCommMonoidToAddCommGroup ℂ

private def threeBlocks {G : Type*} [Group G] {A : Fin 3 → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (r : ∀ i, Representation ℂ G (A i)) : Representation.Equiv
      (FiniteBlockHom.action r) ((r 0).prod ((r 1).prod (r 2))) where
  toLinearEquiv := (Fin.consLinearEquiv ℂ A).symm.trans
    (LinearEquiv.prodCongr (.refl ℂ _) (LinearEquiv.piFinTwo ℂ (fun i => A i.succ)))
  isIntertwining' _ := by ext x <;> rfl

private def fourBlocks {G : Type*} [Group G] {A : Fin 4 → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (r : ∀ i, Representation ℂ G (A i)) : Representation.Equiv
      (FiniteBlockHom.action r) ((r 0).prod ((r 1).prod ((r 2).prod (r 3)))) where
  toLinearEquiv := (Fin.consLinearEquiv ℂ A).symm.trans
    (LinearEquiv.prodCongr (.refl ℂ _)
      ((Fin.consLinearEquiv ℂ (fun i : Fin 3 => A i.succ)).symm.trans
        (LinearEquiv.prodCongr (.refl ℂ _)
          (LinearEquiv.piFinTwo ℂ (fun i : Fin 2 => A i.succ.succ)))))
  isIntertwining' _ := by ext x <;> rfl

private def cg32 : Representation.Equiv
    ((WeakDoubletScalars.doublet.symmetricPower 3).tprod
      (WeakDoubletScalars.doublet.symmetricPower 2))
    ((WeakDoubletScalars.doublet.symmetricPower 5).prod
      ((WeakDoubletScalars.doublet.symmetricPower 3).prod WeakDoubletScalars.doublet)) :=
  (SU2ClebschGordan.equivalence 3 2).symm.trans
    ((threeBlocks (SU2ClebschGordan.summand 3 2)).trans
      (prodEquiv (.refl _) (prodEquiv (.refl _)
        (SymmetricPowerLowDegree.representationOneEquiv WeakDoubletScalars.doublet))))

private def cg22 : Representation.Equiv
    ((WeakDoubletScalars.doublet.symmetricPower 2).tprod
      (WeakDoubletScalars.doublet.symmetricPower 2))
    ((WeakDoubletScalars.doublet.symmetricPower 4).prod
      ((WeakDoubletScalars.doublet.symmetricPower 2).prod
        (trivial ℂ WeakDoubletScalars.Group ℂ))) :=
  (SU2ClebschGordan.equivalence 2 2).symm.trans
    ((threeBlocks (SU2ClebschGordan.summand 2 2)).trans
      (prodEquiv (.refl _) (prodEquiv (.refl _)
        (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet))))

private def cg33 : Representation.Equiv
    ((WeakDoubletScalars.doublet.symmetricPower 3).tprod
      (WeakDoubletScalars.doublet.symmetricPower 3))
    ((WeakDoubletScalars.doublet.symmetricPower 6).prod
      ((WeakDoubletScalars.doublet.symmetricPower 4).prod
        ((WeakDoubletScalars.doublet.symmetricPower 2).prod
          (trivial ℂ WeakDoubletScalars.Group ℂ)))) :=
  (SU2ClebschGordan.equivalence 3 3).symm.trans
    ((fourBlocks (SU2ClebschGordan.summand 3 3)).trans
      (prodEquiv (.refl _) (prodEquiv (.refl _) (prodEquiv (.refl _)
        (SymmetricPowerLowDegree.representationZeroEquiv WeakDoubletScalars.doublet)))))

variable {G : Type*} [Group G] (j : G →* WeakDoubletScalars.Group)
abbrev spin := DoubletQuartic.spin j

def threeTwo : Representation.Equiv (((spin j).symmetricPower 3).tprod ((spin j).symmetricPower 2))
    (((spin j).symmetricPower 5).prod (((spin j).symmetricPower 3).prod (spin j))) :=
  restrictEquiv cg32 j

def twoTwo : Representation.Equiv (((spin j).symmetricPower 2).tprod ((spin j).symmetricPower 2))
    (((spin j).symmetricPower 4).prod
      (((spin j).symmetricPower 2).prod (trivial ℂ G ℂ))) := restrictEquiv cg22 j

def threeThree : Representation.Equiv (((spin j).symmetricPower 3).tprod ((spin j).symmetricPower 3))
    (((spin j).symmetricPower 6).prod (((spin j).symmetricPower 4).prod
      (((spin j).symmetricPower 2).prod (trivial ℂ G ℂ)))) := restrictEquiv cg33 j

end
end Math.DoubletMiddleProducts
