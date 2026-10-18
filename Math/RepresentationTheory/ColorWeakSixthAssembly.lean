import Math.RepresentationTheory.ColorWeakSixthSlices
import Math.RepresentationTheory.SU2IsotypicIdentify

/-! Complete actual Q sixth exterior branching by consecutive retained
weight slices, with all absent odd-spin factors proved zero. -/
namespace Math.ColorWeakSixthAssembly
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open ColorWeakMiddleGauge ColorWeakSixthSlices
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (m : ℕ) : AddCommGroup (Sym[ℂ]^m W) := Module.addCommMonoidToAddCommGroup ℂ
abbrev Retained {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (_r : Representation ℂ Group X) : Type _ := X
@[reducible] local instance : AddCommGroup (Retained zero) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Retained two) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Retained four) := Module.addCommMonoidToAddCommGroup ℂ
abbrev rho := model 6

theorem bounded : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom 6 := by simpa using model_bound 6

abbrev weight (k : ℤ) := TorusWeightSlice.action rho TauCeti.SU2.torusHom k
abbrev multiplicity (k : Fin 7) := SU2IsotypicSlices.multiplicity rho 6 k
abbrev M (k : Fin 7) := SU2IsotypicSlices.M rho 6 k
abbrev canonical := SU2IsotypicSlices.source rho 6
abbrev piece (k : Fin 7) := SU2StringSliceSum.piece multiplicity (SU2IsotypicSlices.degree 6) k

def weight6 : Representation.Equiv (weight 6) six :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 6 0).trans slice6
def weight4 : Representation.Equiv (weight 4) (four.prod six) :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 5 1).trans slice4
def weight2 : Representation.Equiv (weight 2) (two.prod (four.prod six)) :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 4 2).trans slice2
def weight0 : Representation.Equiv (weight 0) (zero.prod (two.prod (four.prod six))) :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 3 3).trans slice0

def multiplicity6 : Representation.Equiv (multiplicity 6) six :=
  SU2IsotypicIdentify.highest rho 6 (model_continuous 6) bounded 6 six weight6
    (SU2ExteriorSliceModels.outside_string gauge basis 6 8 (by
      dsimp [SU2WeightSlice.InString]; omega))
def multiplicity4 : Representation.Equiv (multiplicity 4) four :=
  SU2IsotypicIdentify.equivalence rho 6 (model_continuous 6) bounded 4 four
    (weight4.trans (prodEquiv (.refl _) weight6.symm))
def multiplicity2 : Representation.Equiv (multiplicity 2) two :=
  SU2IsotypicIdentify.equivalence rho 6 (model_continuous 6) bounded 2 two
    (weight2.trans (prodEquiv (.refl _) weight4.symm))
def multiplicity0 : Representation.Equiv (multiplicity 0) zero :=
  SU2IsotypicIdentify.equivalence rho 6 (model_continuous 6) bounded 0 zero
    (weight0.trans (prodEquiv (.refl _) weight2.symm))

theorem odd_multiplicity_zero (k : Fin 7) (hk : k.val%2=1) (x : M k) : x=0 :=
  SU2IsotypicIdentify.zero rho 6 (model_continuous 6) bounded k
    (SU2ExteriorSliceModels.outside_string gauge basis 6 (k.val : ℤ) (by
      dsimp [SU2WeightSlice.InString]; omega)) x

theorem odd_piece_zero (k : Fin 7) (hk : k.val%2=1)
    (x : (Sym[ℂ]^k.val W) ⊗[ℂ] M k) : x=0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [hx, hy, add_zero]
  | tmul v w => rw [odd_multiplicity_zero k hk w, TensorProduct.tmul_zero]

def piece0 : Representation.Equiv (piece 0)
    (external (WeakDoubletScalars.doublet.symmetricPower 0) zero) :=
  SU2IsotypicIdentify.piece rho 6 0 zero multiplicity0
def piece2 : Representation.Equiv (piece 2)
    (external (WeakDoubletScalars.doublet.symmetricPower 2) two) :=
  SU2IsotypicIdentify.piece rho 6 2 two multiplicity2
def piece4 : Representation.Equiv (piece 4)
    (external (WeakDoubletScalars.doublet.symmetricPower 4) four) :=
  SU2IsotypicIdentify.piece rho 6 4 four multiplicity4
def piece6 : Representation.Equiv (piece 6)
    (external (WeakDoubletScalars.doublet.symmetricPower 6) six) :=
  SU2IsotypicIdentify.piece rho 6 6 six multiplicity6

abbrev branches := (external (WeakDoubletScalars.doublet.symmetricPower 0) zero).prod
  ((external (WeakDoubletScalars.doublet.symmetricPower 2) two).prod
    ((external (WeakDoubletScalars.doublet.symmetricPower 4) four).prod
      (external (WeakDoubletScalars.doublet.symmetricPower 6) six)))
abbrev AllCarrier : Type _ := ∀ k : Fin 7, (Sym[ℂ]^k.val W) ⊗[ℂ] M k
abbrev BranchCarrier : Type _ := (Sym[ℂ]^0 W ⊗[ℂ] Retained zero) ×
  ((Sym[ℂ]^2 W ⊗[ℂ] Retained two) × ((Sym[ℂ]^4 W ⊗[ℂ] Retained four) ×
    (Sym[ℂ]^6 W ⊗[ℂ] Retained six)))

def forward : AllCarrier →ₗ[ℂ] BranchCarrier :=
  (piece0.toLinearEquiv.toLinearMap.comp (LinearMap.proj (0 : Fin 7))).prod
    ((piece2.toLinearEquiv.toLinearMap.comp (LinearMap.proj (2 : Fin 7))).prod
      ((piece4.toLinearEquiv.toLinearMap.comp (LinearMap.proj (4 : Fin 7))).prod
        (piece6.toLinearEquiv.toLinearMap.comp (LinearMap.proj (6 : Fin 7)))))

def backward (x : BranchCarrier) : AllCarrier :=
  Fin.cases (piece0.symm x.1) (Fin.cases 0 (Fin.cases (piece2.symm x.2.1)
    (Fin.cases 0 (Fin.cases (piece4.symm x.2.2.1)
      (Fin.cases 0 (Fin.cases (piece6.symm x.2.2.2) (fun i => Fin.elim0 i)))))))

theorem backward_forward (x : AllCarrier) : backward (forward x)=x := by
  funext k
  fin_cases k
  · exact piece0.symm_apply_apply (x 0)
  · exact (odd_piece_zero 1 rfl (x 1)).symm
  · exact piece2.symm_apply_apply (x 2)
  · exact (odd_piece_zero 3 rfl (x 3)).symm
  · exact piece4.symm_apply_apply (x 4)
  · exact (odd_piece_zero 5 rfl (x 5)).symm
  · exact piece6.symm_apply_apply (x 6)

theorem forward_backward (x : BranchCarrier) : forward (backward x)=x :=
  Prod.ext (piece0.apply_symm_apply x.1)
    (Prod.ext (piece2.apply_symm_apply x.2.1)
      (Prod.ext (piece4.apply_symm_apply x.2.2.1) (piece6.apply_symm_apply x.2.2.2)))

def assemble : Representation.Equiv canonical branches where
  toLinearEquiv :=
    { toLinearMap := forward
      invFun := backward
      left_inv := backward_forward
      right_inv := forward_backward }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (piece0.isIntertwining _ _ g (x 0))
      (Prod.ext (piece2.isIntertwining _ _ g (x 2))
        (Prod.ext (piece4.isIntertwining _ _ g (x 4)) (piece6.isIntertwining _ _ g (x 6))))

/-- Complete sixth-degree exterior decomposition, with the actual retained
color/weak modules and all independent spin actions. -/
def equivalence : Representation.Equiv
    ((external WeakDoubletScalars.doublet gauge).exteriorPower 6) branches :=
  (modelEquiv 6).trans
    ((SU2IsotypicSlices.sourceEquivalence rho 6 (model_continuous 6) bounded).symm.trans assemble)

end
end Math.ColorWeakSixthAssembly
