import Math.RepresentationTheory.Exterior.ExteriorSquareCauchy
import Math.RepresentationTheory.Symmetric.SymmetricDualPairing
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Nonzero coupled colored square coefficients with independent spin
factors. Surjective Cauchy projections replace any irreducibility premise
on the symmetric color square. -/
namespace Math.SpinSquarePairing
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

variable {G V B C : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ G V) (b : Representation ℂ G B) (c : Representation ℂ G C)

@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.First (A := V) (B := B)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorSquareCauchy.Second (A := V) (B := B)) := inferInstance

variable (eb : Representation.Equiv (b.exteriorPower 2) (trivial ℂ G ℂ))

def secondEquiv : Representation.Equiv (ExteriorSquareCauchyRepresentation.secondAction a b)
    (a.symmetricPower 2) :=
  (tensorEquiv (.refl (a.symmetricPower 2)) eb).trans
    { toLinearEquiv := TensorProduct.rid ℂ _
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro x z
        change z • (a.symmetricPower 2) g x=(a.symmetricPower 2) g (z • x)
        exact (map_smul _ z x).symm }

def project : IntertwiningMap ((a.tprod b).exteriorPower 2) (a.symmetricPower 2) :=
  (secondEquiv a b eb).toIntertwiningMap.comp (ExteriorSquareCauchyRepresentation.second a b)

theorem project_surjective : Function.Surjective (project a b eb) := by
  intro x
  let e := ExteriorSquareCauchyRepresentation.equivalence a b
  let y := (secondEquiv a b eb).symm x
  refine ⟨e.symm (0,y),?_⟩
  have he := congrArg Prod.snd (e.apply_symm_apply (0,y))
  change ExteriorSquareCauchy.second (e.symm (0,y))=y at he
  change secondEquiv a b eb (ExteriorSquareCauchy.second (e.symm (0,y)))=x
  rw [he]
  exact (secondEquiv a b eb).apply_symm_apply x

variable (ec : Representation.Equiv (c.exteriorPower 2) (trivial ℂ G ℂ))

def coefficient : InvariantCoefficientTransport.Invariants
    (((a.tprod b).exteriorPower 2).tprod ((a.dual.tprod c).exteriorPower 2)) :=
  (SymmetricDualPairing.coefficient a 2).comp ((project a b eb).tensor (project a.dual c ec))

theorem coefficient_nonzero (v : V) (phi : Module.Dual ℂ V) (hv : phi v=1) :
    coefficient a b c eb ec≠0 := by
  obtain ⟨x,hx⟩ := TensorProduct.map_surjective
    (project_surjective a b eb) (project_surjective a.dual c ec)
    (SymmetricPower.tprod ℂ (fun _ : Fin 2 => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin 2 => phi))
  intro hz
  have he := DFunLike.congr_fun hz x
  change SymmetricDualPairing.coefficient a 2
    (((project a b eb).tensor (project a.dual c ec)) x)=0 at he
  change SymmetricDualPairing.coefficient a 2
    ((TensorProduct.map (project a b eb).toLinearMap (project a.dual c ec).toLinearMap) x)=0 at he
  rw [hx,SymmetricDualPairing.coefficient_diagonal,hv,one_pow] at he
  exact one_ne_zero he

include eb ec in
theorem allowed (v : V) (phi : Module.Dual ℂ V) (hv : phi v=1) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (((a.tprod b).exteriorPower 2).tprod ((a.dual.tprod c).exteriorPower 2))) :=
  ⟨coefficient a b c eb ec,coefficient_nonzero a b c eb ec v phi hv⟩

end
end Math.SpinSquarePairing
