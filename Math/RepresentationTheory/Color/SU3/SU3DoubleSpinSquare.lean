import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.Exterior.ExteriorSquareTriple
import Math.RepresentationTheory.Color.SU3.SU3SpinExterior
import Math.RepresentationTheory.Color.SU3.SU3ConjugateSpinExterior

/-! Four actual colored/weak/spin square branches. The two doublet groups
remain independent; no color coupling or irreducibility is assumed. -/
namespace Math.SU3DoubleSpinSquare
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev Group := SU3DefiningExterior.Group × (WeakDoubletScalars.Group × WeakDoubletScalars.Group)
abbrev Color := SU3DefiningExterior.Vector
abbrev Doublet := WeakDoubletScalars.Doublet
abbrev color : Representation ℂ Group Color := SU3DefiningExterior.rho.comp (MonoidHom.fst _ _)
def weakProjection : Group →* WeakDoubletScalars.Group := (MonoidHom.fst _ _).comp (MonoidHom.snd _ _)
def spinProjection : Group →* WeakDoubletScalars.Group := (MonoidHom.snd _ _).comp (MonoidHom.snd _ _)
abbrev weak : Representation ℂ Group Doublet := WeakDoubletScalars.doublet.comp weakProjection
abbrev spin : Representation ℂ Group Doublet := WeakDoubletScalars.doublet.comp spinProjection
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

abbrev tensor := (color.tprod weak).tprod spin
abbrev dualTensor := (color.dual.tprod weak).tprod spin

abbrev pulledDoublet (j : Group →* WeakDoubletScalars.Group) : Representation ℂ Group Doublet :=
  WeakDoubletScalars.doublet.comp j

def top2 (j : Group →* WeakDoubletScalars.Group) : Representation.Equiv
    ((pulledDoublet j).exteriorPower 2) (trivial ℂ Group ℂ) where
  toLinearEquiv := Module.Basis.exteriorPowerTopEquiv (Pi.basisFun ℂ (Fin 2))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have hd : LinearMap.det (WeakDoubletScalars.doublet (j g))=1 := by
      change LinearMap.det (Matrix.toLin' (j g : Matrix (Fin 2) (Fin 2) ℂ))=1
      rw [LinearMap.det_toLin']
      exact (j g).prop.2
    change Module.Basis.exteriorPowerTopEquiv (Pi.basisFun ℂ (Fin 2)) (exteriorPower.map 2 (WeakDoubletScalars.doublet (j g)) x)=_
    rw [Module.Basis.map_exteriorPower_top_eq_det_smul (Pi.basisFun ℂ (Fin 2)),hd,one_smul]
    rfl

def colorTwo : Representation.Equiv (color.exteriorPower 2) color.dual where
  toLinearEquiv := SU3DefiningExterior.twoEquiv.toLinearEquiv
  isIntertwining' g := SU3DefiningExterior.twoEquiv.isIntertwining' g.1

def dualColorTwo : Representation.Equiv (color.dual.exteriorPower 2) color where
  toLinearEquiv := SU3DualExterior.twoEquiv.toLinearEquiv
  isIntertwining' g := SU3DualExterior.twoEquiv.isIntertwining' g.1

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (a : Representation ℂ Group V) (d : Representation ℂ Group W)

abbrev first (d : Representation ℂ Group W) :=
  (d.tprod ((weak.symmetricPower 2).tprod (spin.symmetricPower 2))).prod d
abbrev second (a : Representation ℂ Group V) :=
  ((a.symmetricPower 2).tprod (spin.symmetricPower 2)).prod
    ((a.symmetricPower 2).tprod (weak.symmetricPower 2))

@[reducible] local instance : AddCommGroup (SymmetricSquareCauchy.First (A := Doublet) (B := Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 V) ⊗[ℂ] (SymmetricSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 V) ⊗[ℂ] (SymmetricSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((W) ⊗[ℂ] (SymmetricSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup (SymmetricSquareCauchy.Second (A := Doublet) (B := Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 V) ⊗[ℂ] (SymmetricSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 V) ⊗[ℂ] (SymmetricSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((W) ⊗[ℂ] (SymmetricSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.First (A := Doublet) (B := Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 V) ⊗[ℂ] (ExteriorSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 V) ⊗[ℂ] (ExteriorSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((W) ⊗[ℂ] (ExteriorSquareCauchy.First (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Second (A := Doublet) (B := Doublet)) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 V) ⊗[ℂ] (ExteriorSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((Sym[ℂ]^2 V) ⊗[ℂ] (ExteriorSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance
@[reducible] local instance : AddCommGroup ((W) ⊗[ℂ] (ExteriorSquareCauchy.Second (A := Doublet) (B := Doublet))) := inferInstance

def firstEquiv (e : Representation.Equiv (a.exteriorPower 2) d) :
    Representation.Equiv (ExteriorSquareTriple.first a weak spin) (first d) :=
  SplitRepresentationProjection.prodEquiv
    (tensorEquiv e (.refl _))
    ((tensorEquiv e (tensorEquiv (top2 weakProjection) (top2 spinProjection))).trans
      ((tensorEquiv (.refl d) (Representation.TensorProduct.lid ℂ (trivial ℂ Group ℂ))).trans
        (Representation.TensorProduct.rid ℂ d)))

def secondEquiv : Representation.Equiv (ExteriorSquareTriple.second a weak spin) (second a) :=
  SplitRepresentationProjection.prodEquiv
    ((tensorEquiv (.refl (a.symmetricPower 2)) (tensorEquiv (top2 weakProjection) (.refl _))).trans
      (tensorEquiv (.refl (a.symmetricPower 2)) (Representation.TensorProduct.lid ℂ (spin.symmetricPower 2))))
    ((tensorEquiv (.refl (a.symmetricPower 2)) (tensorEquiv (.refl _) (top2 spinProjection))).trans
      (tensorEquiv (.refl (a.symmetricPower 2)) (Representation.TensorProduct.rid ℂ (weak.symmetricPower 2))))

def square (e : Representation.Equiv (a.exteriorPower 2) d) :
    Representation.Equiv (((a.tprod weak).tprod spin).exteriorPower 2) ((first d).prod (second a)) :=
  ((Representation.TensorProduct.assoc a weak spin).exteriorPower 2).trans
    ((ExteriorSquareTriple.equivalence a weak spin).trans
      (SplitRepresentationProjection.prodEquiv (firstEquiv a d e) (secondEquiv a)))

def positive : Representation.Equiv (tensor.exteriorPower 2) ((first color.dual).prod (second color)) :=
  square color color.dual colorTwo

def negative : Representation.Equiv (dualTensor.exteriorPower 2) ((first color).prod (second color.dual)) :=
  square color.dual color dualColorTwo

end
end Math.SU3DoubleSpinSquare
