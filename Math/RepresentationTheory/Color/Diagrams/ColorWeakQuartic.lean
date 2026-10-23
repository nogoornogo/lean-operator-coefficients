import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Exterior.ExteriorFourthDoubletCauchy
import Math.RepresentationTheory.Exterior.ExteriorCubeDoubletCauchy
import Math.RepresentationTheory.SU2.DoubletQuartic
import Math.RepresentationTheory.Symmetric.SymmetricSquareSum
import Math.RepresentationTheory.Symmetric.SymmetricSquareDual
import Math.RepresentationTheory.Color.Diagrams.DefiningTraceFreeProduct
import Math.RepresentationTheory.SU2.SU2FiniteCoupling
import Math.RepresentationTheory.Exterior.ComplementaryExteriorDuality
import Math.LinearAlgebra.Tensor.TensorDeterminant

/-! Resolve the actual quartic kernels on color tensor a weak doublet.
Every structural comparison is an equivariant equivalence. The final SU3
wrappers discharge the color duality, volume and cubic-hook comparisons. -/
namespace Math.ColorWeakQuartic
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  (r : Representation ℂ G A) (j : G →* WeakDoubletScalars.Group)
abbrev B := WeakDoubletScalars.Doublet
abbrev w := DoubletQuartic.spin j
abbrev gauge := r.tprod (w j)
abbrev adjoint := TraceEndomorphismSplit.traceFreeAction r
abbrev harmonic := SymmetricSquareContractionRepresentation.action r
abbrev squareBranches := (r.dual.tprod ((w j).symmetricPower 2)).prod (r.symmetricPower 2)
abbrev fourthBranches := (r.tprod ((w j).symmetricPower 2)).prod (r.dual.symmetricPower 2)
abbrev cubeBranches := ((w j).symmetricPower 3).prod ((adjoint r).tprod (w j))
abbrev a := r.tprod ((w j).symmetricPower 4)
abbrev b := r.tprod ((w j).symmetricPower 2)
abbrev c := (harmonic r).tprod ((w j).symmetricPower 2)
abbrev d := (r.dual.symmetricPower 2).tprod ((w j).symmetricPower 2)
abbrev k211Branches := (a r j).prod
  (((c r j).prod (harmonic r)).prod ((d r j).prod ((b r j).prod r)))

abbrev CommonCarrier := (A ⊗[ℂ] Sym[ℂ]^2 B) × Sym[ℂ]^2 (Module.Dual ℂ A)
abbrev K211Carrier := (A ⊗[ℂ] Sym[ℂ]^4 B) ×
  (((SymmetricSquareContraction.Kernel (A := A) ⊗[ℂ] Sym[ℂ]^2 B) ×
    SymmetricSquareContraction.Kernel (A := A)) ×
      ((Sym[ℂ]^2 (Module.Dual ℂ A) ⊗[ℂ] Sym[ℂ]^2 B) × ((A ⊗[ℂ] Sym[ℂ]^2 B) × A)))
@[reducible] local instance : AddCommGroup (CommonCarrier (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (K211Carrier (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.K211 (A := A ⊗[ℂ] B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

@[reducible] local instance : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricSquareContraction.Kernel (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Sym[ℂ]^2 (Module.Dual ℂ A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (ExteriorFourthKernels.Source13 (A := A ⊗[ℂ] B)) := inferInstance

variable (two : Representation.Equiv (r.exteriorPower 2) r.dual)

def square : Representation.Equiv ((gauge r j).exteriorPower 2) (squareBranches r j) :=
  (ExteriorSquareCauchyRepresentation.equivalence r (w j)).trans
    (prodEquiv (tensorEquiv two (.refl _))
      ((tensorEquiv (.refl (r.symmetricPower 2)) (DoubletCubicHook.top2 j)).trans
        (Representation.TensorProduct.rid ℂ (r.symmetricPower 2))))

def weakSquareDual : Representation.Equiv ((w j).symmetricPower 2) ((w j).symmetricPower 2).dual :=
  { toLinearEquiv := (SU2FiniteCoupling.selfDual 2).toLinearEquiv
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change SU2FiniteCoupling.selfDual 2
          ((WeakDoubletScalars.doublet.symmetricPower 2) (j g) x) y=
        SU2FiniteCoupling.selfDual 2 x
          ((WeakDoubletScalars.doublet.symmetricPower 2) (j g⁻¹) y)
      rw [map_inv]
      exact congrArg (fun f => f y)
        ((SU2FiniteCoupling.selfDual 2).isIntertwining _ _ (j g) x) }

def fourthDual : Representation.Equiv (squareBranches r j).dual (fourthBranches r j) :=
  (dualProdEquiv (r.dual.tprod ((w j).symmetricPower 2)) (r.symmetricPower 2)).symm.trans
    (prodEquiv ((InvariantTensorCurry.tensorDual r.dual ((w j).symmetricPower 2)).symm.trans
      (tensorEquiv (bidualEquiv r).symm (weakSquareDual j).symm))
        (SymmetricSquareDual.equivalence r).symm)

variable (dim : Module.finrank ℂ A=3) (det : ∀ g, LinearMap.det (r g)=1)

include dim in
theorem gauge_dimension : Module.finrank ℂ (A ⊗[ℂ] B)=6 := by
  rw [Module.finrank_tensorProduct, dim]
  norm_num [B, WeakDoubletScalars.Doublet]

include det in
theorem gauge_determinant (g : G) : LinearMap.det (gauge r j g)=1 :=
  TensorDeterminant.map_one (Module.finBasis ℂ A) (Pi.basisFun ℂ (Fin 2))
    (r g) (w j g) (det g) (ExteriorCubeDoubletRepresentation.spin_determinant j g)

def fourth : Representation.Equiv ((gauge r j).exteriorPower 4) (fourthBranches r j) :=
  (ComplementaryExteriorDuality.equiv (gauge r j) (gauge_determinant r j det)
    (Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ (A ⊗[ℂ] B)))
    (by rw [gauge_dimension (A := A) dim] : 4+2=Module.finrank ℂ (A ⊗[ℂ] B))).trans
      ((dualEquiv (square r j two)).trans (fourthDual r j))

variable (top : Representation.Equiv (r.exteriorPower 3) (trivial ℂ G ℂ))
  (hook : Representation.Equiv (ExteriorCubeHookRepresentation.action r) (adjoint r))

def cube : Representation.Equiv ((gauge r j).exteriorPower 3) (cubeBranches r j) :=
  (ExteriorCubeDoubletCauchyRepresentation.equivalence r j).symm.trans
    (prodEquiv ((tensorEquiv top (.refl _)).trans
      (Representation.TensorProduct.lid ℂ ((w j).symmetricPower 3)))
        (tensorEquiv hook (.refl _)))

def source13First : Representation.Equiv
    ((gauge r j).tprod ((w j).symmetricPower 3)) ((a r j).prod (b r j)) :=
  (Representation.TensorProduct.assoc r (w j) ((w j).symmetricPower 3)).trans
    ((tensorEquiv (.refl r) (DoubletQuartic.tensorCube j)).trans
      (TensorProductSums.prodRight r ((w j).symmetricPower 4) ((w j).symmetricPower 2)))

variable (dualTwo : Representation.Equiv (r.dual.exteriorPower 2) r)

abbrev source13SecondBranches := ((c r j).prod (harmonic r)).prod
  (((d r j).prod (r.dual.symmetricPower 2)).prod ((b r j).prod r))

def expandScalar {U : Type*} [AddCommMonoid U] [Module ℂ U] (s : Representation ℂ G U) :
    Representation.Equiv (s.tprod (((w j).symmetricPower 2).prod (trivial ℂ G ℂ)))
      ((s.tprod ((w j).symmetricPower 2)).prod s) :=
  (TensorProductSums.prodRight s ((w j).symmetricPower 2) (trivial ℂ G ℂ)).trans
    (prodEquiv (.refl _) (Representation.TensorProduct.rid ℂ s))

def source13Second : Representation.Equiv
    ((gauge r j).tprod ((adjoint r).tprod (w j))) (source13SecondBranches r j) :=
  (regroupPairDiagonal r (adjoint r) (w j) (w j)).trans
    ((tensorEquiv (DefiningTraceFreeProduct.equivalence r (by rw [dim]; decide) two dualTwo)
      (DoubletQuartic.tensorSquare j)).trans
        ((TensorProductSums.prodLeft (harmonic r) ((r.dual.symmetricPower 2).prod r) _).trans
          (prodEquiv (expandScalar j (harmonic r))
            ((TensorProductSums.prodLeft (r.dual.symmetricPower 2) r _).trans
              (prodEquiv (expandScalar j (r.dual.symmetricPower 2)) (expandScalar j r))))))

def source13Expand : Representation.Equiv
    (ExteriorFourthKernelsRepresentation.source13 (gauge r j))
    (((a r j).prod (b r j)).prod (source13SecondBranches r j)) :=
  (tensorEquiv (.refl (gauge r j)) (cube r j top hook)).trans
    ((TensorProductSums.prodRight (gauge r j) ((w j).symmetricPower 3) ((adjoint r).tprod (w j))).trans
      (prodEquiv (source13First r j) (source13Second r j two dim dualTwo)))

def source13Reorder : Representation.Equiv
    (((a r j).prod (b r j)).prod (source13SecondBranches r j))
    ((k211Branches r j).prod (fourthBranches r j)) where
  toLinearEquiv :=
    { toFun x := ((x.1.1,(x.2.1,(x.2.2.1.1,x.2.2.2))),(x.1.2,x.2.2.1.2))
      invFun x := ((x.1.1,x.2.1),(x.1.2.1,((x.1.2.2.1,x.2.2),x.1.2.2.2)))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def kernel211 : Representation.Equiv (ExteriorFourthKernelsRepresentation.action211 (gauge r j))
    (k211Branches r j) := by
  let e := (TensorProductSums.prodComm
    (ExteriorFourthKernelsRepresentation.action211 (gauge r j)) (fourthBranches r j)).trans
      ((prodEquiv (fourth r j two dim det).symm (.refl _)).trans
        ((ExteriorFourthKernelsRepresentation.split13 (gauge r j)).symm.trans
          ((source13Expand r j two dim top hook dualTwo).trans (source13Reorder r j))))
  exact Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := ExteriorFourthKernels.K211 (A := A ⊗[ℂ] B))
    (B := K211Carrier (A := A)) (C := CommonCarrier (A := A))
    (ExteriorFourthKernelsRepresentation.action211 (gauge r j))
    (k211Branches r j) (fourthBranches r j) e)

abbrev e := (r.dual.symmetricPower 2).tprod ((w j).symmetricPower 4)
abbrev k22Branches := ((e r j).prod (r.dual.symmetricPower 2)).prod
  (((b r j).prod (c r j)).prod (r.symmetricPower 4))
abbrev K22Carrier := ((Sym[ℂ]^2 (Module.Dual ℂ A) ⊗[ℂ] Sym[ℂ]^4 B) ×
    Sym[ℂ]^2 (Module.Dual ℂ A)) ×
  (((A ⊗[ℂ] Sym[ℂ]^2 B) ×
    (SymmetricSquareContraction.Kernel (A := A) ⊗[ℂ] Sym[ℂ]^2 B)) × (Sym[ℂ]^4 A))
@[reducible] local instance : AddCommGroup (K22Carrier (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.K22 (A := A ⊗[ℂ] B)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.Source22 (A := A ⊗[ℂ] B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def symmetricColorSquare : Representation.Equiv ((r.symmetricPower 2).symmetricPower 2)
    ((r.symmetricPower 4).prod (r.dual.symmetricPower 2)) :=
  (SymmetricFourth22Representation.equivalence r).trans
    (prodEquiv (.refl _) ((SymmetricFourth22Representation.kernelFull r
      (by rw [dim]; decide)).trans (two.symmetricPower 2)))

def source22First : Representation.Equiv
    ((r.dual.tprod ((w j).symmetricPower 2)).symmetricPower 2)
    (((e r j).prod (r.dual.symmetricPower 2)).prod (b r j)) :=
  (SymmetricSquareCauchyRepresentation.equivalence r.dual ((w j).symmetricPower 2)).trans
    (prodEquiv
      ((tensorEquiv (.refl (r.dual.symmetricPower 2)) (DoubletQuartic.symmetricSpinOne j)).trans
        ((TensorProductSums.prodRight (r.dual.symmetricPower 2)
          ((w j).symmetricPower 4) (trivial ℂ G ℂ)).trans
            (prodEquiv (.refl _) (Representation.TensorProduct.rid ℂ (r.dual.symmetricPower 2)))))
      (tensorEquiv dualTwo (DoubletQuartic.exteriorSpinOne j)))

def source22Mixed : Representation.Equiv
    ((r.dual.tprod ((w j).symmetricPower 2)).tprod (r.symmetricPower 2))
    ((b r j).prod (c r j)) :=
  (Representation.TensorProduct.comm _ _).trans
    ((Representation.TensorProduct.assoc (r.symmetricPower 2) r.dual ((w j).symmetricPower 2)).symm.trans
      ((tensorEquiv (SymmetricSquareContractionRepresentation.equivalence r) (.refl _)).trans
        (TensorProductSums.prodLeft r (harmonic r) ((w j).symmetricPower 2))))

abbrev source22Branches := (((e r j).prod (r.dual.symmetricPower 2)).prod (b r j)).prod
  (((b r j).prod (c r j)).prod ((r.symmetricPower 4).prod (r.dual.symmetricPower 2)))

def source22Expand : Representation.Equiv
    (ExteriorFourthKernelsRepresentation.source22 (gauge r j)) (source22Branches r j) :=
  ((square r j two).symmetricPower 2).trans
    ((SymmetricSquareSum.equivalence (r.dual.tprod ((w j).symmetricPower 2)) (r.symmetricPower 2)).trans
      (prodEquiv (source22First r j dualTwo)
        (prodEquiv (source22Mixed r j) (symmetricColorSquare r two dim))))

def source22Reorder : Representation.Equiv (source22Branches r j)
    ((k22Branches r j).prod (fourthBranches r j)) where
  toLinearEquiv :=
    { toFun x := ((x.1.1,(x.2.1,x.2.2.1)),(x.1.2,x.2.2.2))
      invFun x := ((x.1.1,x.2.1),(x.1.2.1,(x.1.2.2,x.2.2)))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def kernel22 : Representation.Equiv (ExteriorFourthKernelsRepresentation.action22 (gauge r j))
    (k22Branches r j) := by
  let h := (TensorProductSums.prodComm
    (ExteriorFourthKernelsRepresentation.action22 (gauge r j)) (fourthBranches r j)).trans
      ((prodEquiv (fourth r j two dim det).symm (.refl _)).trans
        ((ExteriorFourthKernelsRepresentation.split22 (gauge r j)).symm.trans
          ((source22Expand r j two dim dualTwo).trans (source22Reorder r j))))
  exact Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := ExteriorFourthKernels.K22 (A := A ⊗[ℂ] B))
    (B := K22Carrier (A := A)) (C := CommonCarrier (A := A))
    (ExteriorFourthKernelsRepresentation.action22 (gauge r j))
    (k22Branches r j) (fourthBranches r j) h)

variable (s : G →* WeakDoubletScalars.Group)
abbrev spin := DoubletQuartic.spin s
abbrev quarticBranches :=
  ((fourthBranches r j).tprod ((spin s).symmetricPower 4)).prod
    (((k211Branches r j).tprod ((spin s).symmetricPower 2)).prod (k22Branches r j))

/-- Complete color/weak resolution of the quartic doublet source. The
two SU2 homomorphisms may be independent factors of the retained group. -/
def quartic : Representation.Equiv (((gauge r j).tprod (spin s)).exteriorPower 4)
    (quarticBranches r j s) :=
  (ExteriorFourthDoubletCauchyRepresentation.equivalence (gauge r j) s).symm.trans
    (prodEquiv (tensorEquiv (fourth r j two dim det) (.refl _))
      (prodEquiv (tensorEquiv (kernel211 r j two dim det top hook dualTwo) (.refl _))
        (kernel22 r j two dim det dualTwo)))

end
end Math.ColorWeakQuartic
