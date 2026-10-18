import Math.RepresentationTheory.RestrictedColorVertices
import Math.RepresentationTheory.TraceFreeColorVertex
import Math.RepresentationTheory.ColorTreeDiagrams
import Math.RepresentationTheory.DualMixedTensorSwap

/-! Actual color vertices with raw retractions and incident-flag preimages.
This data supplies the constructive direction of the diagram criterion;
necessity additionally uses the separate symmetry and trace proofs. -/
namespace Math.ColorFlagVertex
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior SplitRepresentationProjection ExternalInvariantTensor
open scoped TensorProduct

structure Vertex where
  positive : ℕ
  negative : ℕ
  Carrier : Type
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  action : Representation ℂ Group Carrier
  split : Split (SU3TensorPositive.mixed positive negative) action
  flag : ∀ (v : Vector) (f : Module.Dual ℂ Vector), f v = 0 → Carrier
  flag_embed : ∀ (v : Vector) (f : Module.Dual ℂ Vector) (hf : f v = 0),
    split.embed (flag v f hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin positive => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin negative => f)
attribute [instance] Vertex.additive Vertex.linear

instance finite (v : Vertex) : Module.Finite ℂ v.Carrier :=
  Module.Finite.of_surjective v.split.project.toLinearMap
    (fun x => ⟨v.split.embed x,v.split.left_inv x⟩)

def alongEquiv {A : Type} [AddCommGroup A] [Module ℂ A]
    (v : Vertex) (a : Representation ℂ Group A) (e : Representation.Equiv v.action a) : Vertex where
  positive := v.positive
  negative := v.negative
  Carrier := A
  action := a
  split := v.split.trans (Split.ofEquiv e)
  flag x f hf := e (v.flag x f hf)
  flag_embed x f hf := by
    change v.split.embed (e.symm (e (v.flag x f hf))) = _
    rw [Representation.Equiv.symm_apply_apply]
    exact v.flag_embed x f hf

def square : Vertex where
  positive := 2
  negative := 1
  Carrier := (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule
  additive := Module.addCommMonoidToAddCommGroup ℂ
  action := SymmetricSquareContractionRepresentation.action rho
  split := RestrictedColorVertices.square rho
  flag := RestrictedColorVertices.squareFlag rho
  flag_embed := RestrictedColorVertices.square_flag_embed rho

def cube : Vertex where
  positive := 3
  negative := 1
  Carrier := (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule
  additive := Module.addCommMonoidToAddCommGroup ℂ
  action := SymmetricCubeContractionRepresentation.action rho
  split := RestrictedColorVertices.cube rho
  flag := RestrictedColorVertices.cubeFlag rho
  flag_embed := RestrictedColorVertices.cube_flag_embed rho

def squareSquare : Vertex where
  positive := 2
  negative := 2
  Carrier := (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule
  additive := Module.addCommMonoidToAddCommGroup ℂ
  action := SymmetricSquarePartialTraceRepresentation.action rho
  split := RestrictedColorVertices.squareSquare rho
  flag := RestrictedColorVertices.squareSquareFlag rho
  flag_embed := RestrictedColorVertices.squareSquare_flag_embed rho

theorem dimension_ne_zero : Module.finrank ℂ Vector ≠ 0 := by rw [dimension]; decide

def adjoint : Vertex where
  positive := 1
  negative := 1
  Carrier := TraceEndomorphismSplit.TraceFree rho
  action := TraceEndomorphismSplit.traceFreeAction rho
  split := TraceFreeColorVertex.split rho dimension_ne_zero
  flag := TraceFreeColorVertex.flag rho
  flag_embed := TraceFreeColorVertex.flag_embed rho dimension_ne_zero

@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n Vector) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n (Module.Dual ℂ Vector)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

def positiveSymmetricSplit (n : ℕ) : Split (SU3TensorPositive.mixed n 0) (rho.symmetricPower n) :=
  ((Split.ofEquiv (tensorEquiv (.refl (rho.tensorPower n))
    (TensorVolumeSplit.zeroEquivalence rho.dual))).trans
      (Split.ofEquiv (Representation.TensorProduct.rid ℂ (rho.tensorPower n)))).trans
        (SymmetricTensorSplit.split rho n)

def negativeSymmetricSplit (n : ℕ) : Split (SU3TensorPositive.mixed 0 n) (rho.dual.symmetricPower n) :=
  ((Split.ofEquiv (tensorEquiv (TensorVolumeSplit.zeroEquivalence rho)
    (.refl (rho.dual.tensorPower n)))).trans
      (Split.ofEquiv (Representation.TensorProduct.lid ℂ (rho.dual.tensorPower n)))).trans
        (SymmetricTensorSplit.split rho.dual n)

theorem positiveSymmetric_flag (n : ℕ) (v : Vector) (f : Module.Dual ℂ Vector) :
    (positiveSymmetricSplit n).embed (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin 0 => f) := by
  change TensorProduct.map LinearMap.id
    (TensorVolumeSplit.zeroEquivalence rho.dual).symm.toLinearEquiv.toLinearMap
      ((Representation.TensorProduct.rid ℂ (rho.tensorPower n)).symm
        (SymmetricTensorSplit.sectionMap rho n (SymmetricPower.tprod ℂ (fun _ : Fin n => v)))) = _
  rw [SymmetricTensorSplit.section_pure_power]
  simp [TensorVolumeSplit.zeroEquivalence]
  congr 1
  change (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => Module.Dual ℂ Vector)).symm 1 = _
  apply (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => Module.Dual ℂ Vector)).injective
  rw [LinearEquiv.apply_symm_apply]
  simp

theorem negativeSymmetric_flag (n : ℕ) (v : Vector) (f : Module.Dual ℂ Vector) :
    (negativeSymmetricSplit n).embed (SymmetricPower.tprod ℂ (fun _ : Fin n => f)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin 0 => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin n => f) := by
  change TensorProduct.map (TensorVolumeSplit.zeroEquivalence rho).symm.toLinearEquiv.toLinearMap
    LinearMap.id
      ((Representation.TensorProduct.lid ℂ (rho.dual.tensorPower n)).symm
        (SymmetricTensorSplit.sectionMap rho.dual n (SymmetricPower.tprod ℂ (fun _ : Fin n => f)))) = _
  rw [SymmetricTensorSplit.section_pure_power]
  simp [TensorVolumeSplit.zeroEquivalence]
  congr 1
  change (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => Vector)).symm 1 = _
  apply (PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => Vector)).injective
  rw [LinearEquiv.apply_symm_apply]
  simp

def positiveSymmetric (n : ℕ) : Vertex where
  positive := n
  negative := 0
  Carrier := Sym[ℂ]^n Vector
  action := rho.symmetricPower n
  split := positiveSymmetricSplit n
  flag v _ _ := SymmetricPower.tprod ℂ (fun _ : Fin n => v)
  flag_embed v f _ := positiveSymmetric_flag n v f

def negativeSymmetric (n : ℕ) : Vertex where
  positive := 0
  negative := n
  Carrier := Sym[ℂ]^n (Module.Dual ℂ Vector)
  action := rho.dual.symmetricPower n
  split := negativeSymmetricSplit n
  flag _ f _ := SymmetricPower.tprod ℂ (fun _ : Fin n => f)
  flag_embed v f _ := negativeSymmetric_flag n v f

def ofDual {A : Type} [AddCommGroup A] [Module ℂ A]
    (p q : ℕ) (r : Representation ℂ Group A)
    (S : Split ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q)) r)
    (flagD : ∀ (f : Module.Dual ℂ Vector) (v : Module.Dual ℂ (Module.Dual ℂ Vector)), v f = 0 → A)
    (he : ∀ f v (hf : v f = 0), S.embed (flagD f v hf) =
      PiTensorProduct.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => v)) : Vertex where
  positive := q
  negative := p
  Carrier := A
  action := r
  split := (Split.ofEquiv (DualMixedTensorSwap.equivalence rho p q).symm).trans S
  flag v f hf := flagD f (Module.Dual.eval ℂ Vector v) hf
  flag_embed v f hf := by
    change DualMixedTensorSwap.equivalence rho p q
      (S.embed (flagD f (Module.Dual.eval ℂ Vector v) hf)) = _
    have hp := he f (Module.Dual.eval ℂ Vector v) hf
    exact (congrArg (DualMixedTensorSwap.equivalence rho p q) hp).trans
      (DualMixedTensorSwap.tprod rho p q (fun _ => v) (fun _ => f))

@[reducible] local instance : AddCommGroup
    (SymmetricSquareContractionRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricCubeContractionRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (SymmetricSquarePartialTraceRepresentation.kernel rho.dual).toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ

def oppositeSquare : Vertex := ofDual 2 1
  (SymmetricSquareContractionRepresentation.action rho.dual) (RestrictedColorVertices.square rho.dual)
  (RestrictedColorVertices.squareFlag rho.dual) (RestrictedColorVertices.square_flag_embed rho.dual)

def oppositeCube : Vertex := ofDual 3 1
  (SymmetricCubeContractionRepresentation.action rho.dual) (RestrictedColorVertices.cube rho.dual)
  (RestrictedColorVertices.cubeFlag rho.dual) (RestrictedColorVertices.cube_flag_embed rho.dual)

def oppositeSquareSquare : Vertex := ofDual 2 2
  (SymmetricSquarePartialTraceRepresentation.action rho.dual) (RestrictedColorVertices.squareSquare rho.dual)
  (RestrictedColorVertices.squareSquareFlag rho.dual) (RestrictedColorVertices.squareSquare_flag_embed rho.dual)

def squareDual : Vertex := alongEquiv oppositeSquare
  (SymmetricSquareContractionRepresentation.action rho).dual (RestrictedColorDuality.square rho).symm

def cubeDual : Vertex := alongEquiv oppositeCube
  (SymmetricCubeContractionRepresentation.action rho).dual (RestrictedColorDuality.cube rho).symm

def squareSquareDual : Vertex := alongEquiv oppositeSquareSquare
  (SymmetricSquarePartialTraceRepresentation.action rho).dual (RestrictedColorDuality.squareSquare rho).symm

def symmetricDual (n : ℕ) : Vertex := alongEquiv (negativeSymmetric n) (rho.symmetricPower n).dual
  (SymmetricPowerDualEquivalence.equivalence rho n)

theorem dual_dimension_ne_zero : Module.finrank ℂ (Module.Dual ℂ Vector) ≠ 0 := by
  rw [Subspace.dual_finrank_eq]
  exact dimension_ne_zero

def oppositeAdjoint : Vertex := ofDual 1 1
  (TraceEndomorphismSplit.traceFreeAction rho.dual)
  (TraceFreeColorVertex.split rho.dual dual_dimension_ne_zero)
  (TraceFreeColorVertex.flag rho.dual)
  (TraceFreeColorVertex.flag_embed rho.dual dual_dimension_ne_zero)

def adjointDual : Vertex := alongEquiv oppositeAdjoint
  (TraceEndomorphismSplit.traceFreeAction rho).dual (RestrictedColorDuality.adjoint rho dimension_ne_zero).symm

def oppositeSymmetricDual (n : ℕ) : Vertex := alongEquiv (positiveSymmetric n)
  (rho.dual.symmetricPower n).dual
    (((SplitRepresentationProjection.bidualEquiv rho).symmetricPower n).trans
      (SymmetricPowerDualEquivalence.equivalence rho.dual n))

def oppositeSquareDual : Vertex := by
  letI : AddCommGroup (SymmetricSquareContractionRepresentation.kernel rho).toSubmodule := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module.Finite ℂ ((SymmetricSquareContractionRepresentation.kernel rho).toSubmodule) := finite square
  exact alongEquiv square
    (SymmetricSquareContractionRepresentation.action rho.dual).dual
      ((SplitRepresentationProjection.bidualEquiv
        (SymmetricSquareContractionRepresentation.action rho)).trans
          (SplitRepresentationProjection.dualEquiv (RestrictedColorDuality.square rho)))

def oppositeCubeDual : Vertex := by
  letI : AddCommGroup (SymmetricCubeContractionRepresentation.kernel rho).toSubmodule := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module.Finite ℂ ((SymmetricCubeContractionRepresentation.kernel rho).toSubmodule) := finite cube
  exact alongEquiv cube
    (SymmetricCubeContractionRepresentation.action rho.dual).dual
      ((SplitRepresentationProjection.bidualEquiv
        (SymmetricCubeContractionRepresentation.action rho)).trans
          (SplitRepresentationProjection.dualEquiv (RestrictedColorDuality.cube rho)))

def oppositeSquareSquareDual : Vertex := by
  letI : AddCommGroup (SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module.Finite ℂ ((SymmetricSquarePartialTraceRepresentation.kernel rho).toSubmodule) := finite squareSquare
  exact alongEquiv squareSquare
    (SymmetricSquarePartialTraceRepresentation.action rho.dual).dual
      ((SplitRepresentationProjection.bidualEquiv
        (SymmetricSquarePartialTraceRepresentation.action rho)).trans
          (SplitRepresentationProjection.dualEquiv (RestrictedColorDuality.squareSquare rho)))

def oppositeAdjointDual : Vertex := by
  letI : AddCommGroup (TraceEndomorphismSplit.TraceFree rho) := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module.Finite ℂ (TraceEndomorphismSplit.TraceFree rho) := finite adjoint
  exact alongEquiv adjoint
    (TraceEndomorphismSplit.traceFreeAction rho.dual).dual
      ((SplitRepresentationProjection.bidualEquiv
        (TraceEndomorphismSplit.traceFreeAction rho)).trans
          (SplitRepresentationProjection.dualEquiv (RestrictedColorDuality.adjoint rho dimension_ne_zero)))

end
end Math.ColorFlagVertex
