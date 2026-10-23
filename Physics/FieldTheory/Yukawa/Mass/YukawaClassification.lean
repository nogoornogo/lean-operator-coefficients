import Physics.FieldTheory.Yukawa.Mass.SymmetricScalarYukawa

/-! Exact parameterization of scalar-linear symmetric invariant Yukawa
couplings. No irreducibility or finite-dimensionality is required. -/
set_option autoImplicit false
namespace Physics.YukawaClassification
noncomputable section
open Representation WeylYukawaMass SymmetricScalarYukawa

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup V] [Module ℂ V]
  (rhoS : Representation ℂ G S) (rhoV : Representation ℂ G V)

def toMap (Y : EquivariantYukawa rhoS rhoV) :
    IntertwiningMap rhoS (scalarRho rhoV) where
  toLinearMap := Y.toLinearMap.codRestrict (symmetricForms rhoV).toSubmodule Y.symmetric
  isIntertwining' g := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Y.toLinearMap (rhoS g s) x y =
      Y.toLinearMap s (rhoV g⁻¹ x) (rhoV g⁻¹ y)
    simpa using Y.invariant g s (rhoV g⁻¹ x) (rhoV g⁻¹ y)

def ofMap (f : IntertwiningMap rhoS (scalarRho rhoV)) :
    EquivariantYukawa rhoS rhoV where
  toLinearMap := (symmetricForms rhoV).toSubmodule.subtype.comp f.toLinearMap
  symmetric s := (f s).property
  invariant g s x y := by
    change (f (rhoS g s)).val (rhoV g x) (rhoV g y) = (f s).val x y
    rw [f.isIntertwining rhoS (scalarRho rhoV)]
    simp

theorem ofMap_toMap (Y : EquivariantYukawa rhoS rhoV) :
    ofMap rhoS rhoV (toMap rhoS rhoV Y) = Y := by
  cases Y
  rfl

theorem toMap_ofMap (f : IntertwiningMap rhoS (scalarRho rhoV)) :
    toMap rhoS rhoV (ofMap rhoS rhoV f) = f := by
  ext s
  rfl

def equiv : EquivariantYukawa rhoS rhoV ≃ IntertwiningMap rhoS (scalarRho rhoV) where
  toFun := toMap rhoS rhoV
  invFun := ofMap rhoS rhoV
  left_inv := ofMap_toMap rhoS rhoV
  right_inv := toMap_ofMap rhoS rhoV

theorem evaluation (Y : EquivariantYukawa rhoS rhoV) (s : S) :
    (toMap rhoS rhoV Y s).val = Y.toLinearMap s := rfl

def endomorphismEquiv (e : Representation.Equiv (scalarRho rhoV) rhoS) :
    EquivariantYukawa rhoS rhoV ≃ IntertwiningMap (scalarRho rhoV) (scalarRho rhoV) where
  toFun Y := (toMap rhoS rhoV Y).comp e.toIntertwiningMap
  invFun f := ofMap rhoS rhoV (f.comp e.symm.toIntertwiningMap)
  left_inv Y := by
    apply (equiv rhoS rhoV).injective
    change toMap rhoS rhoV (ofMap rhoS rhoV _) = toMap rhoS rhoV Y
    rw [toMap_ofMap]
    apply DFunLike.ext
    intro s
    change toMap rhoS rhoV Y (e (e.symm s)) = toMap rhoS rhoV Y s
    rw [Representation.Equiv.apply_symm_apply]
  right_inv f := by
    change (toMap rhoS rhoV (ofMap rhoS rhoV (f.comp e.symm.toIntertwiningMap))).comp
      e.toIntertwiningMap = f
    rw [toMap_ofMap]
    apply DFunLike.ext
    intro s
    change f (e.symm (e s)) = f s
    rw [Representation.Equiv.symm_apply_apply]

def scalarMultiple (Y : EquivariantYukawa rhoS rhoV) (c : ℂ) :
    EquivariantYukawa rhoS rhoV where
  toLinearMap := c • Y.toLinearMap
  symmetric s := (Y.symmetric s).smul c
  invariant g s x y := by
    change c * Y.toLinearMap (rhoS g s) (rhoV g x) (rhoV g y) =
      c * Y.toLinearMap s x y
    rw [Y.invariant]

theorem scalarMultiple_apply (Y : EquivariantYukawa rhoS rhoV) (c : ℂ) (s : S) (x y : V) :
    (scalarMultiple rhoS rhoV Y c).toLinearMap s x y = c * Y.toLinearMap s x y := rfl

end
end Physics.YukawaClassification
