import Math.RepresentationTheory.Color.Diagrams.ColorWeakMiddleGauge
import Math.RepresentationTheory.SU2.DoubletMiddleProducts

/-! Actual retained color/weak source comparisons for the four
nonnegative spin-weight slices of the Q sixth exterior power. -/
namespace Math.ColorWeakSixthSlices
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection ColorWeakMiddleGauge
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev e (n : ℕ) := adjoint.tprod (spin n)
abbrev c (n : ℕ) := (color.symmetricPower 3).tprod (spin n)
abbrev d (n : ℕ) := (color.dual.symmetricPower 3).tprod (spin n)
abbrev h (n : ℕ) := balancedKernel.tprod (spin n)
abbrev six := scalar
abbrev four := (spin 2).prod ((e 2).prod adjoint)
abbrev two := (spin 4).prod ((e 4).prod ((e 2).prod ((e 2).prod
  (scalar.prod (adjoint.prod ((c 2).prod ((d 2).prod balancedKernel)))))))
abbrev zero := (spin 6).prod ((spin 2).prod ((e 4).prod ((e 2).prod
  ((color.symmetricPower 3).prod ((color.dual.symmetricPower 3).prod (h 2))))))
abbrev source4 := (gauge.exteriorPower 5).tprod (gauge.exteriorPower 1)
abbrev source2 := (gauge.exteriorPower 4).tprod (gauge.exteriorPower 2)
abbrev source0 := (gauge.exteriorPower 3).tprod (gauge.exteriorPower 3)
abbrev expanded4 := ((spin 2).prod scalar).prod ((e 2).prod adjoint)

def slice6 : Representation.Equiv
    ((gauge.exteriorPower 6).tprod (gauge.exteriorPower 0)) six :=
  (tensorEquiv sixth gauge.exteriorPowerZeroEquiv).trans (Representation.TensorProduct.rid ℂ scalar)

def colorPair : Representation.Equiv (color.tprod color.dual) (scalar.prod adjoint) :=
  restrictEquiv SU3ColorPair.equivalence colorProjection
def dualColorPair : Representation.Equiv (color.dual.tprod color) (scalar.prod adjoint) :=
  (Representation.TensorProduct.comm color.dual color).trans colorPair

def expand4 : Representation.Equiv source4 expanded4 :=
  (tensorEquiv fifth gauge.exteriorPowerOneEquiv).trans
    ((regroupPairDiagonal color.dual color weak weak).trans
    ((tensorEquiv dualColorPair (DoubletQuartic.tensorSquare weakProjection)).trans
    ((TensorProductSums.expand scalar adjoint (spin 2) scalar).trans
      (prodEquiv
        (prodEquiv (Representation.TensorProduct.lid ℂ (spin 2)) (Representation.TensorProduct.lid ℂ scalar))
        (prodEquiv (.refl _) (Representation.TensorProduct.rid ℂ adjoint))))))

def reorder4 : Representation.Equiv expanded4 (four.prod six) where
  toLinearEquiv :=
    { toFun x := ((x.1.1,(x.2.1,x.2.2)),x.1.2)
      invFun x := ((x.1.1,x.2),(x.1.2.1,x.1.2.2))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def slice4 : Representation.Equiv source4 (four.prod six) := expand4.trans reorder4

def definingSquare : Representation.Equiv (color.tprod (color.symmetricPower 2))
    ((color.symmetricPower 3).prod adjoint) :=
  restrictEquiv SU3MiddleColor.definingSquare colorProjection
def dualDefiningSquare : Representation.Equiv (color.dual.tprod (color.dual.symmetricPower 2))
    ((color.dual.symmetricPower 3).prod adjoint) :=
  restrictEquiv SU3MiddleColor.dualDefiningSquare colorProjection
def squareDualSquare : Representation.Equiv
    ((color.symmetricPower 2).tprod (color.dual.symmetricPower 2))
    ((scalar.prod adjoint).prod balancedKernel) :=
  restrictEquiv SU3MiddleColor.squareDualSquare colorProjection

abbrev first2Branches := ((spin 4).prod ((spin 2).prod scalar)).prod
  ((e 4).prod ((e 2).prod adjoint))

def first2 : Representation.Equiv
    ((color.tprod (spin 2)).tprod (color.dual.tprod (spin 2))) first2Branches :=
  (regroupPairDiagonal color color.dual (spin 2) (spin 2)).trans
    ((tensorEquiv colorPair (DoubletMiddleProducts.twoTwo weakProjection)).trans
    ((TensorProductSums.prodLeft scalar adjoint ((spin 4).prod ((spin 2).prod scalar))).trans
      (prodEquiv
        (Representation.TensorProduct.lid ℂ ((spin 4).prod ((spin 2).prod scalar)))
        ((TensorProductSums.prodRight adjoint (spin 4) ((spin 2).prod scalar)).trans
          (prodEquiv (.refl _) (ColorWeakQuartic.expandScalar weakProjection adjoint))))))

def second2 : Representation.Equiv
    ((color.tprod (spin 2)).tprod (color.symmetricPower 2)) ((c 2).prod (e 2)) :=
  (Representation.TensorProduct.assoc color (spin 2) (color.symmetricPower 2)).trans
    ((tensorEquiv (.refl color) (Representation.TensorProduct.comm (spin 2) (color.symmetricPower 2))).trans
    ((Representation.TensorProduct.assoc color (color.symmetricPower 2) (spin 2)).symm.trans
    ((tensorEquiv definingSquare (.refl (spin 2))).trans
      (TensorProductSums.prodLeft (color.symmetricPower 3) adjoint (spin 2)))))

def third2 : Representation.Equiv
    ((color.dual.symmetricPower 2).tprod (color.dual.tprod (spin 2))) ((d 2).prod (e 2)) :=
  (Representation.TensorProduct.assoc (color.dual.symmetricPower 2) color.dual (spin 2)).symm.trans
    ((tensorEquiv
      ((Representation.TensorProduct.comm (color.dual.symmetricPower 2) color.dual).trans dualDefiningSquare)
      (.refl (spin 2))).trans
      (TensorProductSums.prodLeft (color.dual.symmetricPower 3) adjoint (spin 2)))

def fourth2 : Representation.Equiv
    ((color.dual.symmetricPower 2).tprod (color.symmetricPower 2))
    ((scalar.prod adjoint).prod balancedKernel) :=
  (Representation.TensorProduct.comm (color.dual.symmetricPower 2) (color.symmetricPower 2)).trans squareDualSquare

abbrev expanded2 := (first2Branches.prod ((c 2).prod (e 2))).prod
  (((d 2).prod (e 2)).prod ((scalar.prod adjoint).prod balancedKernel))

def expand2 : Representation.Equiv source2 expanded2 :=
  (tensorEquiv fourth square).trans
    ((TensorProductSums.expand (color.tprod (spin 2)) (color.dual.symmetricPower 2)
      (color.dual.tprod (spin 2)) (color.symmetricPower 2)).trans
      (prodEquiv (prodEquiv first2 second2) (prodEquiv third2 fourth2)))

def reorder2 : Representation.Equiv expanded2 (two.prod expanded4) where
  toLinearEquiv :=
    { toFun x := ((x.1.1.1.1,(x.1.1.2.1,(x.1.1.2.2.1,(x.1.2.2,(x.1.1.1.2.2,(x.1.1.2.2.2,(x.1.2.1,(x.2.1.1,x.2.2.2)))))))),((x.1.1.1.2.1,x.2.2.1.1),(x.2.1.2,x.2.2.1.2)))
      invFun x := ((((x.1.1,(x.2.1.1,x.1.2.2.2.2.1)),(x.1.2.1,(x.1.2.2.1,x.1.2.2.2.2.2.1))),(x.1.2.2.2.2.2.2.1,x.1.2.2.2.1)),((x.1.2.2.2.2.2.2.2.1,x.2.2.1),((x.2.1.2,x.2.2.2),x.1.2.2.2.2.2.2.2.2)))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def resolve2 : Representation.Equiv expanded2 (two.prod (four.prod six)) :=
  reorder2.trans (prodEquiv (.refl _) reorder4)

def slice2 : Representation.Equiv source2 (two.prod (four.prod six)) := expand2.trans resolve2

abbrev first0Branches := (spin 6).prod ((spin 4).prod ((spin 2).prod scalar))
abbrev cross0Branches := (e 4).prod (e 2)
abbrev common0Branches := (((spin 2).prod scalar).prod ((e 2).prod adjoint)).prod
  ((e 2).prod adjoint)
abbrev rest0Branches := (((c 2).prod (color.symmetricPower 3)).prod
  ((d 2).prod (color.dual.symmetricPower 3))).prod ((h 2).prod balancedKernel)
abbrev fourth0Branches := common0Branches.prod rest0Branches

def first0 : Representation.Equiv ((spin 3).tprod (spin 3)) first0Branches :=
  DoubletMiddleProducts.threeThree weakProjection

def weak31 : Representation.Equiv ((spin 3).tprod weak) ((spin 4).prod (spin 2)) :=
  (Representation.TensorProduct.comm (spin 3) weak).trans (DoubletQuartic.tensorCube weakProjection)

def second0 : Representation.Equiv ((spin 3).tprod (adjoint.tprod weak)) cross0Branches :=
  (Representation.TensorProduct.assoc (spin 3) adjoint weak).symm.trans
    ((tensorEquiv (Representation.TensorProduct.comm (spin 3) adjoint) (.refl weak)).trans
    ((Representation.TensorProduct.assoc adjoint (spin 3) weak).trans
    ((tensorEquiv (.refl adjoint) weak31).trans
      (TensorProductSums.prodRight adjoint (spin 4) (spin 2)))))

def third0 : Representation.Equiv ((adjoint.tprod weak).tprod (spin 3)) cross0Branches :=
  (Representation.TensorProduct.assoc adjoint weak (spin 3)).trans
    ((tensorEquiv (.refl adjoint) (DoubletQuartic.tensorCube weakProjection)).trans
      (TensorProductSums.prodRight adjoint (spin 4) (spin 2)))

def common0 : Representation.Equiv
    (((scalar.prod adjoint).prod adjoint).tprod ((spin 2).prod scalar)) common0Branches :=
  (TensorProductSums.prodLeft (scalar.prod adjoint) adjoint ((spin 2).prod scalar)).trans
    (prodEquiv
      ((TensorProductSums.prodLeft scalar adjoint ((spin 2).prod scalar)).trans
        (prodEquiv (Representation.TensorProduct.lid ℂ ((spin 2).prod scalar))
          (ColorWeakQuartic.expandScalar weakProjection adjoint)))
      (ColorWeakQuartic.expandScalar weakProjection adjoint))

def rest0 : Representation.Equiv
    ((((color.symmetricPower 3).prod (color.dual.symmetricPower 3)).prod balancedKernel).tprod
      ((spin 2).prod scalar)) rest0Branches :=
  (TensorProductSums.prodLeft ((color.symmetricPower 3).prod (color.dual.symmetricPower 3))
    balancedKernel ((spin 2).prod scalar)).trans
    (prodEquiv
      ((TensorProductSums.prodLeft (color.symmetricPower 3) (color.dual.symmetricPower 3)
        ((spin 2).prod scalar)).trans
        (prodEquiv (ColorWeakQuartic.expandScalar weakProjection (color.symmetricPower 3))
          (ColorWeakQuartic.expandScalar weakProjection (color.dual.symmetricPower 3))))
      (ColorWeakQuartic.expandScalar weakProjection balancedKernel))

def fourth0 : Representation.Equiv ((adjoint.tprod weak).tprod (adjoint.tprod weak)) fourth0Branches :=
  (regroupPairDiagonal adjoint adjoint weak weak).trans
    ((tensorEquiv adjointPair (DoubletQuartic.tensorSquare weakProjection)).trans
    ((TensorProductSums.prodLeft ((scalar.prod adjoint).prod adjoint)
      (((color.symmetricPower 3).prod (color.dual.symmetricPower 3)).prod balancedKernel)
      ((spin 2).prod scalar)).trans (prodEquiv common0 rest0)))

abbrev expanded0 := (first0Branches.prod cross0Branches).prod (cross0Branches.prod fourth0Branches)

def expand0 : Representation.Equiv source0 expanded0 :=
  (tensorEquiv cube cube).trans
    ((TensorProductSums.expand (spin 3) (adjoint.tprod weak) (spin 3) (adjoint.tprod weak)).trans
      (prodEquiv (prodEquiv first0 second0) (prodEquiv third0 fourth0)))

def reorder0 : Representation.Equiv expanded0 (zero.prod expanded2) where
  toLinearEquiv :=
    { toFun x := ((x.1.1.1,(x.1.1.2.2.1,(x.1.2.1,(x.1.2.2,(x.2.2.2.1.1.2,(x.2.2.2.1.2.2,x.2.2.2.2.1)))))),((((x.1.1.2.1,(x.2.2.1.1.1.1,x.1.1.2.2.2)),(x.2.1.1,(x.2.1.2,x.2.2.1.1.2.2))),(x.2.2.2.1.1.1,x.2.2.1.1.2.1)),((x.2.2.2.1.2.1,x.2.2.1.2.1),((x.2.2.1.1.1.2,x.2.2.1.2.2),x.2.2.2.2.2))))
      invFun x := (((x.1.1,(x.2.1.1.1.1,(x.1.2.1,x.2.1.1.1.2.2))),(x.1.2.2.1,x.1.2.2.2.1)),((x.2.1.1.2.1,x.2.1.1.2.2.1),((((x.2.1.1.1.2.1,x.2.2.2.1.1),(x.2.1.2.2,x.2.1.1.2.2.2)),(x.2.2.1.2,x.2.2.2.1.2)),(((x.2.1.2.1,x.1.2.2.2.2.1),(x.2.2.1.1,x.1.2.2.2.2.2.1)),(x.1.2.2.2.2.2.2,x.2.2.2.2)))))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def slice0 : Representation.Equiv source0 (zero.prod (two.prod (four.prod six))) :=
  (expand0.trans reorder0).trans (prodEquiv (.refl _) resolve2)

end
end Math.ColorWeakSixthSlices
