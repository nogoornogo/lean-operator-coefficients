import Math.RepresentationTheory.ExteriorSquareCauchy
import Math.RepresentationTheory.SymmetricSquareCauchy
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! Complete four-branch square decomposition for three retained factors.
All maps are built from proved Cauchy inverses, without branching premises. -/
namespace Math.ExteriorSquareTriple
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G A B C : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ G A) (b : Representation ℂ G B) (c : Representation ℂ G C)

def prodRight : Representation.Equiv (a.tprod (b.prod c)) ((a.tprod b).prod (a.tprod c)) where
  toLinearEquiv := TensorProduct.prodRight ℂ ℂ A B C
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    apply Prod.ext <;> rfl

abbrev first := ((a.exteriorPower 2).tprod ((b.symmetricPower 2).tprod (c.symmetricPower 2))).prod
  ((a.exteriorPower 2).tprod ((b.exteriorPower 2).tprod (c.exteriorPower 2)))
abbrev second := ((a.symmetricPower 2).tprod ((b.exteriorPower 2).tprod (c.symmetricPower 2))).prod
  ((a.symmetricPower 2).tprod ((b.symmetricPower 2).tprod (c.exteriorPower 2)))

@[reducible] local instance : AddCommGroup
    (ExteriorSquareCauchy.First (A := A) (B := B ⊗[ℂ] C)) := inferInstance
@[reducible] local instance : AddCommGroup
    (ExteriorSquareCauchy.Second (A := A) (B := B ⊗[ℂ] C)) := inferInstance

@[reducible] local instance : AddCommGroup (SymmetricSquareCauchy.First (A := B) (B := C)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 A) ⊗[ℂ] (SymmetricSquareCauchy.First (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 A) ⊗[ℂ] (SymmetricSquareCauchy.First (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricSquareCauchy.Second (A := B) (B := C)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 A) ⊗[ℂ] (SymmetricSquareCauchy.Second (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 A) ⊗[ℂ] (SymmetricSquareCauchy.Second (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.First (A := B) (B := C)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 A) ⊗[ℂ] (ExteriorSquareCauchy.First (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 A) ⊗[ℂ] (ExteriorSquareCauchy.First (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Second (A := B) (B := C)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 A) ⊗[ℂ] (ExteriorSquareCauchy.Second (A := B) (B := C))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 A) ⊗[ℂ] (ExteriorSquareCauchy.Second (A := B) (B := C))) := inferInstance

def firstEquiv : Representation.Equiv
    (ExteriorSquareCauchyRepresentation.firstAction a (b.tprod c)) (first a b c) :=
  (tensorEquiv (.refl (a.exteriorPower 2))
    (SymmetricSquareCauchyRepresentation.equivalence b c)).trans
      (prodRight (a.exteriorPower 2)
        (SymmetricSquareCauchyRepresentation.firstAction b c)
        (SymmetricSquareCauchyRepresentation.secondAction b c))

def secondEquiv : Representation.Equiv
    (ExteriorSquareCauchyRepresentation.secondAction a (b.tprod c)) (second a b c) :=
  (tensorEquiv (.refl (a.symmetricPower 2))
    (ExteriorSquareCauchyRepresentation.equivalence b c)).trans
      (prodRight (a.symmetricPower 2)
        (ExteriorSquareCauchyRepresentation.firstAction b c)
        (ExteriorSquareCauchyRepresentation.secondAction b c))

def equivalence : Representation.Equiv ((a.tprod (b.tprod c)).exteriorPower 2)
    ((first a b c).prod (second a b c)) :=
  (ExteriorSquareCauchyRepresentation.equivalence a (b.tprod c)).trans
    (SplitRepresentationProjection.prodEquiv (firstEquiv a b c) (secondEquiv a b c))

end
end Math.ExteriorSquareTriple
