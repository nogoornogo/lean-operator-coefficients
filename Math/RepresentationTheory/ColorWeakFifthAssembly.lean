import Math.RepresentationTheory.ColorWeakFifthSlices
import Math.RepresentationTheory.SU2IsotypicIdentify

/-! Complete actual Q fifth exterior branching: the color/weak slices
identify all retained spin multiplicities, and the canonical isotypic
decomposition is assembled with its absent even-spin factors removed. -/
namespace Math.ColorWeakFifthAssembly
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open ColorWeakMiddleGauge ColorWeakFifthSlices
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (m : ℕ) : AddCommGroup (Sym[ℂ]^m W) :=
  Module.addCommMonoidToAddCommGroup ℂ
abbrev Retained {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (_r : Representation ℂ Group X) : Type _ := X
@[reducible] local instance : AddCommGroup (Retained one) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Retained three) := Module.addCommMonoidToAddCommGroup ℂ
abbrev rho := model 5

theorem bounded : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom 5 := by simpa using model_bound 5

abbrev weight (k : ℤ) := TorusWeightSlice.action rho TauCeti.SU2.torusHom k
abbrev multiplicity (k : Fin 6) := SU2IsotypicSlices.multiplicity rho 5 k
abbrev M (k : Fin 6) := SU2IsotypicSlices.M rho 5 k
abbrev canonical := SU2IsotypicSlices.source rho 5
abbrev piece (k : Fin 6) := SU2StringSliceSum.piece (multiplicity) (SU2IsotypicSlices.degree 5) k

def weight5 : Representation.Equiv (weight 5) five :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 5 0).trans slice5
def weight3 : Representation.Equiv (weight 3) (three.prod five) :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 4 1).trans slice3
def weight1 : Representation.Equiv (weight 1) (one.prod (three.prod five)) :=
  (SU2ExteriorSliceModels.weightEquivalence gauge basis 3 2).trans slice1

def multiplicity5 : Representation.Equiv (multiplicity 5) five :=
  SU2IsotypicIdentify.highest rho 5 (model_continuous 5) bounded 5 five weight5
    (SU2ExteriorSliceModels.outside_string gauge basis 5 7 (by
      dsimp [SU2WeightSlice.InString]; omega))

def multiplicity3 : Representation.Equiv (multiplicity 3) three :=
  SU2IsotypicIdentify.equivalence rho 5 (model_continuous 5) bounded 3 three
    (weight3.trans (prodEquiv (.refl _) weight5.symm))

def multiplicity1 : Representation.Equiv (multiplicity 1) one :=
  SU2IsotypicIdentify.equivalence rho 5 (model_continuous 5) bounded 1 one
    (weight1.trans (prodEquiv (.refl _) weight3.symm))

theorem even_multiplicity_zero (k : Fin 6) (hk : k.val%2=0) (x : M k) : x=0 :=
  SU2IsotypicIdentify.zero rho 5 (model_continuous 5) bounded k
    (SU2ExteriorSliceModels.outside_string gauge basis 5 (k.val : ℤ) (by
      dsimp [SU2WeightSlice.InString]; omega)) x

theorem even_piece_zero (k : Fin 6) (hk : k.val%2=0)
    (x : (Sym[ℂ]^k.val W) ⊗[ℂ] M k) : x=0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [hx, hy, add_zero]
  | tmul v w => rw [even_multiplicity_zero k hk w, TensorProduct.tmul_zero]

def piece1 : Representation.Equiv (piece 1)
    (external (WeakDoubletScalars.doublet.symmetricPower 1) one) :=
  SU2IsotypicIdentify.piece rho 5 1 one multiplicity1
def piece3 : Representation.Equiv (piece 3)
    (external (WeakDoubletScalars.doublet.symmetricPower 3) three) :=
  SU2IsotypicIdentify.piece rho 5 3 three multiplicity3
def piece5 : Representation.Equiv (piece 5)
    (external (WeakDoubletScalars.doublet.symmetricPower 5) five) :=
  SU2IsotypicIdentify.piece rho 5 5 five multiplicity5

abbrev branches := (external (WeakDoubletScalars.doublet.symmetricPower 1) one).prod
  ((external (WeakDoubletScalars.doublet.symmetricPower 3) three).prod
    (external (WeakDoubletScalars.doublet.symmetricPower 5) five))

abbrev AllCarrier : Type _ := ∀ k : Fin 6, (Sym[ℂ]^k.val W) ⊗[ℂ] M k
abbrev BranchCarrier : Type _ := (Sym[ℂ]^1 W ⊗[ℂ] Retained one) ×
  ((Sym[ℂ]^3 W ⊗[ℂ] Retained three) × (Sym[ℂ]^5 W ⊗[ℂ] Retained five))

def forward : AllCarrier →ₗ[ℂ] BranchCarrier :=
  (piece1.toLinearEquiv.toLinearMap.comp (LinearMap.proj (1 : Fin 6))).prod
    ((piece3.toLinearEquiv.toLinearMap.comp (LinearMap.proj (3 : Fin 6))).prod
      (piece5.toLinearEquiv.toLinearMap.comp (LinearMap.proj (5 : Fin 6))))

def backward (x : BranchCarrier) : AllCarrier :=
  Fin.cases 0 (Fin.cases (piece1.symm x.1)
    (Fin.cases 0 (Fin.cases (piece3.symm x.2.1)
      (Fin.cases 0 (Fin.cases (piece5.symm x.2.2) (fun i => Fin.elim0 i))))))

theorem backward_forward (x : AllCarrier) : backward (forward x)=x := by
  funext k
  fin_cases k
  · exact (even_piece_zero 0 rfl (x 0)).symm
  · exact piece1.symm_apply_apply (x 1)
  · exact (even_piece_zero 2 rfl (x 2)).symm
  · exact piece3.symm_apply_apply (x 3)
  · exact (even_piece_zero 4 rfl (x 4)).symm
  · exact piece5.symm_apply_apply (x 5)

theorem forward_backward (x : BranchCarrier) : forward (backward x)=x :=
  Prod.ext (piece1.apply_symm_apply x.1)
    (Prod.ext (piece3.apply_symm_apply x.2.1) (piece5.apply_symm_apply x.2.2))

def assemble : Representation.Equiv canonical branches where
  toLinearEquiv :=
    { toLinearMap := forward
      invFun := backward
      left_inv := backward_forward
      right_inv := forward_backward }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (piece1.isIntertwining _ _ g (x 1))
      (Prod.ext (piece3.isIntertwining _ _ g (x 3)) (piece5.isIntertwining _ _ g (x 5)))

/-- Complete source equivalence, with every color, weak and independent
spin action retained, and with no supplied branching comparison. -/
def equivalence : Representation.Equiv
    ((external WeakDoubletScalars.doublet gauge).exteriorPower 5) branches :=
  (modelEquiv 5).trans
    ((SU2IsotypicSlices.sourceEquivalence rho 5 (model_continuous 5) bounded).symm.trans assemble)

end
end Math.ColorWeakFifthAssembly
