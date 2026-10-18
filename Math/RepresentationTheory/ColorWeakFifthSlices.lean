import Math.RepresentationTheory.ColorWeakMiddleGauge
import Math.RepresentationTheory.DoubletMiddleProducts

/-! Actual retained color/weak decompositions of the three nonnegative
spin-weight slices in the Q fifth exterior power. -/
namespace Math.ColorWeakFifthSlices
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection ColorWeakMiddleGauge
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev a (n : ℕ) := (color.symmetricPower 2).tprod (spin n)
abbrev d (n : ℕ) := color.dual.tprod (spin n)
abbrev h (n : ℕ) := dualHarmonic.tprod (spin n)
abbrev p (n : ℕ) := cubicKernel.tprod (spin n)
abbrev a1 := (color.symmetricPower 2).tprod weak
abbrev d1 := color.dual.tprod weak
abbrev h1 := dualHarmonic.tprod weak
abbrev p1 := cubicKernel.tprod weak
abbrev five := d1
abbrev three := (a 3).prod ((d 3).prod (a1.prod (d1.prod h1)))
abbrev one := (d 5).prod ((d 3).prod (d1.prod
  ((a 3).prod (a1.prod ((h 3).prod (h1.prod p1))))))
abbrev source3 := (gauge.exteriorPower 4).tprod (gauge.exteriorPower 1)
abbrev source1 := (gauge.exteriorPower 3).tprod (gauge.exteriorPower 2)
abbrev expanded3 := (((a 3).prod a1).prod ((d 3).prod d1)).prod (d1.prod h1)

def slice5 : Representation.Equiv
    ((gauge.exteriorPower 5).tprod (gauge.exteriorPower 0)) five :=
  (tensorEquiv fifth gauge.exteriorPowerZeroEquiv).trans
    (Representation.TensorProduct.rid ℂ five)

def weak21 : Representation.Equiv ((spin 2).tprod weak) ((spin 3).prod weak) :=
  (Representation.TensorProduct.comm (spin 2) weak).trans
    (DoubletCubicHook.symmetricSource weakProjection)

def first3 : Representation.Equiv ((color.tprod (spin 2)).tprod gauge)
    (((a 3).prod a1).prod ((d 3).prod d1)) :=
  (regroupPairDiagonal color color (spin 2) weak).trans
    ((tensorEquiv
      ((SymmetricExteriorSquare.equivalence color).trans (prodEquiv (.refl _) colorTwo))
      weak21).trans
      (TensorProductSums.expand (color.symmetricPower 2) color.dual (spin 3) weak))

def dualSquareDefining : Representation.Equiv
    ((color.dual.symmetricPower 2).tprod color) (color.dual.prod dualHarmonic) :=
  (tensorEquiv (.refl (color.dual.symmetricPower 2)) (bidualEquiv color)).trans
    (SymmetricSquareContractionRepresentation.equivalence color.dual)

def second3 : Representation.Equiv ((color.dual.symmetricPower 2).tprod gauge) (d1.prod h1) :=
  (Representation.TensorProduct.assoc (color.dual.symmetricPower 2) color weak).symm.trans
    ((tensorEquiv dualSquareDefining (.refl weak)).trans
      (TensorProductSums.prodLeft color.dual dualHarmonic weak))

def expand3 : Representation.Equiv source3 expanded3 :=
  (tensorEquiv fourth gauge.exteriorPowerOneEquiv).trans
    ((TensorProductSums.prodLeft (color.tprod (spin 2)) (color.dual.symmetricPower 2) gauge).trans
      (prodEquiv first3 second3))

def reorder3 : Representation.Equiv expanded3 (three.prod five) where
  toLinearEquiv :=
    { toFun x := ((x.1.1.1,(x.1.2.1,(x.1.1.2,(x.1.2.2,x.2.2)))),x.2.1)
      invFun x := (((x.1.1,x.1.2.2.1),(x.1.2.1,x.1.2.2.2.1)),(x.2,x.1.2.2.2.2))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def slice3 : Representation.Equiv source3 (three.prod five) := expand3.trans reorder3

def first1 : Representation.Equiv ((spin 3).tprod (color.dual.tprod (spin 2)))
    ((d 5).prod ((d 3).prod d1)) :=
  (Representation.TensorProduct.assoc (spin 3) color.dual (spin 2)).symm.trans
    ((tensorEquiv (Representation.TensorProduct.comm (spin 3) color.dual) (.refl (spin 2))).trans
    ((Representation.TensorProduct.assoc color.dual (spin 3) (spin 2)).trans
    ((tensorEquiv (.refl color.dual) (DoubletMiddleProducts.threeTwo weakProjection)).trans
      ((TensorProductSums.prodRight color.dual (spin 5) ((spin 3).prod weak)).trans
        (prodEquiv (.refl _) (TensorProductSums.prodRight color.dual (spin 3) weak))))))

abbrev third1Branches := ((h 3).prod h1).prod
  (((a 3).prod a1).prod ((d 3).prod d1))

def third1 : Representation.Equiv ((adjoint.tprod weak).tprod (color.dual.tprod (spin 2)))
    third1Branches :=
  (regroupPairDiagonal adjoint color.dual weak (spin 2)).trans
    ((tensorEquiv adjointDual (DoubletCubicHook.symmetricSource weakProjection)).trans
    ((TensorProductSums.prodLeft dualHarmonic
      ((color.symmetricPower 2).prod color.dual) ((spin 3).prod weak)).trans
      (prodEquiv (TensorProductSums.prodRight dualHarmonic (spin 3) weak)
        ((TensorProductSums.prodLeft (color.symmetricPower 2) color.dual ((spin 3).prod weak)).trans
          (prodEquiv (TensorProductSums.prodRight (color.symmetricPower 2) (spin 3) weak)
            (TensorProductSums.prodRight color.dual (spin 3) weak))))))

abbrev fourth1Branches := p1.prod (h1.prod (a1.prod d1))

def fourth1 : Representation.Equiv ((adjoint.tprod weak).tprod (color.symmetricPower 2))
    fourth1Branches :=
  (Representation.TensorProduct.assoc adjoint weak (color.symmetricPower 2)).trans
    ((tensorEquiv (.refl adjoint) (Representation.TensorProduct.comm weak (color.symmetricPower 2))).trans
    ((Representation.TensorProduct.assoc adjoint (color.symmetricPower 2) weak).symm.trans
    ((tensorEquiv adjointSquare (.refl weak)).trans
    ((TensorProductSums.prodLeft cubicKernel
      (dualHarmonic.prod ((color.symmetricPower 2).prod color.dual)) weak).trans
      (prodEquiv (.refl _)
        ((TensorProductSums.prodLeft dualHarmonic ((color.symmetricPower 2).prod color.dual) weak).trans
          (prodEquiv (.refl _)
            (TensorProductSums.prodLeft (color.symmetricPower 2) color.dual weak))))))))

abbrev expanded1 := (((d 5).prod ((d 3).prod d1)).prod (a 3)).prod
  (third1Branches.prod fourth1Branches)

def expand1 : Representation.Equiv source1 expanded1 :=
  (tensorEquiv cube square).trans
    ((TensorProductSums.expand (spin 3) (adjoint.tprod weak)
      (color.dual.tprod (spin 2)) (color.symmetricPower 2)).trans
      (prodEquiv (prodEquiv first1 (Representation.TensorProduct.comm (spin 3) (color.symmetricPower 2)))
        (prodEquiv third1 fourth1)))

def reorder1 : Representation.Equiv expanded1 (one.prod expanded3) where
  toLinearEquiv :=
    { toFun x :=
        ((x.1.1.1,(x.1.1.2.1,(x.1.1.2.2,
          (x.1.2,(x.2.1.2.1.2,(x.2.1.1.1,(x.2.1.1.2,x.2.2.1))))))),
        (((x.2.1.2.1.1,x.2.2.2.2.1),(x.2.1.2.2.1,x.2.1.2.2.2)),
          (x.2.2.2.2.2,x.2.2.2.1)))
      invFun x :=
        (((x.1.1,(x.1.2.1,x.1.2.2.1)),x.1.2.2.2.1),
          (((x.1.2.2.2.2.2.1,x.1.2.2.2.2.2.2.1),
            ((x.2.1.1.1,x.1.2.2.2.2.1),x.2.1.2)),
            (x.1.2.2.2.2.2.2.2,(x.2.2.2,(x.2.1.1.2,x.2.2.1)))))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

def slice1 : Representation.Equiv source1 (one.prod (three.prod five)) :=
  (expand1.trans reorder1).trans (prodEquiv (.refl _) reorder3)

end
end Math.ColorWeakFifthSlices
