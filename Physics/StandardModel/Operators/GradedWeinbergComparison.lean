import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.RepresentationTheory.TypedMixedSeparatedHom
import Math.LinearAlgebra.LinearEquivComparison
import Mathlib.Tactic.IrreducibleDef

open Math

/-! The actual LLHH sector as a consumer of arbitrary-degree separated completeness. -/
namespace GUT.GradedWeinbergComparison
set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor
open scoped TensorProduct
variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

@[reducible] local instance : AddCommGroup (Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup (WeinbergModelSector.Lepton F) := inferInstance
@[reducible] local instance : AddCommGroup
    ((⋀[ℂ]^2 (WeinbergModelSector.Lepton F)) ⊗[ℂ] Sym[ℂ]^2 Weak) := inferInstance

abbrev LocalGroup := TwoComponentContractions.WeakGroup × WeylSpinor.Group
def localLepton (_ : Unit) := external DipoleGaugeTensor.weak WeylSpinor.left
def localHiggs (_ : Unit) := DipoleGaugeTensor.weak.comp (MonoidHom.fst _ WeylSpinor.Group)
def flavor (_ : Unit) := a
def scalarFlavor (_ : Unit) := trivial ℂ R ℂ
def pattern (_ : Fin 2) : Unit := ()

abbrev fermion := TypedMixedSeparatedHom.fieldF localLepton (flavor a)
abbrev boson := TypedMixedSeparatedHom.fieldB localHiggs (scalarFlavor (R := R))
abbrev Residual := IntertwiningMap
  (TypedMixedSeparatedHom.residual localLepton localHiggs (flavor a)
    (scalarFlavor (R := R)) pattern pattern) (trivial ℂ R ℂ)

def leptonEquiv : Representation.Equiv
    (FiniteSpeciesExterior.representation (fermion a)) (WeinbergModelSector.lepton a) where
  toLinearEquiv := LinearEquiv.piUnique ℂ (fun _ : Unit => WeinbergModelSector.Lepton F)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change fermion a () g (v ()) = WeinbergModelSector.lepton a g (v ())
    have he : fermion a () = WeinbergModelSector.lepton a := by
      ext ⟨g,r⟩ : 1
      apply TensorProduct.ext'
      intro x y
      simp [fermion, TypedMixedSeparatedHom.fieldF, TypedMixedLocalHom.fermion,
        TypedMixedSeparatedHom.localF, TypedMixedSeparatedHom.residualF,
        CommutingActionHom.action_apply, flavor, localLepton,
        WeinbergModelSector.lepton, external, Representation.tprod_apply]
    rw [he]

def higgsEquiv : Representation.Equiv
    (FiniteSpeciesExterior.representation (boson (R := R)))
    (WeinbergModelSector.higgs (R := R)) where
  toLinearEquiv := (LinearEquiv.piUnique ℂ (fun _ : Unit => Weak ⊗[ℂ] ℂ)).trans
    (TensorProduct.rid ℂ Weak)
  isIntertwining' g := by
    rcases g with ⟨⟨g,s⟩,r⟩
    apply LinearMap.ext
    intro v
    change TensorProduct.rid ℂ Weak (boson () ((g,s),r) (v ())) =
      WeinbergModelSector.higgs ((g,s),r) (TensorProduct.rid ℂ Weak (v ()))
    induction v () using TensorProduct.inductionOn with
    | tmul x z =>
      simp [boson, TypedMixedSeparatedHom.fieldB, TypedMixedLocalHom.boson,
        TypedMixedSeparatedHom.localB, TypedMixedSeparatedHom.residualB,
        CommutingActionHom.action_apply, scalarFlavor, localHiggs,
        WeinbergModelSector.higgs, Representation.tprod_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
def domainEquiv : Representation.Equiv
    (((FiniteSpeciesExterior.representation (fermion a)).exteriorPower 2).tprod
      ((FiniteSpeciesExterior.representation (boson (R := R))).symmetricPower 2))
    (((WeinbergModelSector.lepton a).exteriorPower 2).tprod
      ((WeinbergModelSector.higgs (R := R)).symmetricPower 2)) :=
  tensorEquiv ((leptonEquiv a).exteriorPower 2)
  ((higgsEquiv (R := R)).symmetricPower 2)

theorem domainEquiv_pure (v : Fin 2 → Unit → WeinbergModelSector.Lepton F)
    (w : Fin 2 → Unit → Weak ⊗[ℂ] ℂ) :
    domainEquiv a (MixedWeightSupport.pure v w) =
      MixedWeightSupport.pure (fun i => v i ())
        (fun j => TensorProduct.rid ℂ Weak (w j ())) := by
  change (leptonEquiv a).exteriorPower 2 (exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ]
    (higgsEquiv (R := R)).symmetricPower 2 (SymmetricPower.tprod ℂ w) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.symmetricPower_apply_tprod]
  rfl

def inputEquiv : WeinbergModelSector.ModelSector a ≃ₗ[ℂ]
    MixedPatternAssembly.familySpace (fermion a) (boson (R := R)) pattern pattern where
  toFun f := ⟨InvariantCoefficientTransport.alongEquiv (domainEquiv a).symm f, by
    intro labels scalars hout
    have hl : labels = pattern := funext (fun _ => Subsingleton.elim _ _)
    have hs : scalars = pattern := funext (fun _ => Subsingleton.elim _ _)
    exact False.elim (hout ⟨⟨1, by simpa using hl⟩, ⟨1, by simpa using hs⟩⟩)⟩
  invFun f := InvariantCoefficientTransport.alongEquiv (domainEquiv a) f.val
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg f ((domainEquiv a).toLinearEquiv.apply_symm_apply x)
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg f.val ((domainEquiv a).toLinearEquiv.symm_apply_apply x)
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' z f := by apply Subtype.ext; rfl

def equiv : WeinbergModelSector.ModelSector a ≃ₗ[ℂ] Residual a :=
  (inputEquiv a).trans (TypedMixedSeparatedHom.familyEquiv localLepton localHiggs
    (flavor a) (scalarFlavor (R := R)) pattern pattern)

theorem inputEquiv_pure (f : WeinbergModelSector.ModelSector a)
    (v : Fin 2 → WeinbergModelSector.Lepton F) (h : Fin 2 → Weak) :
    (inputEquiv a f).val (MixedWeightSupport.pure
      (fun i => Pi.single () (v i)) (fun j => Pi.single () (h j ⊗ₜ[ℂ] (1 : ℂ)))) =
      f (MixedWeightSupport.pure v h) := by
  change f (domainEquiv a (MixedWeightSupport.pure _ _)) = _
  rw [domainEquiv_pure]
  simp

attribute [local irreducible] inputEquiv equiv

irreducible_def onSMEquiv : WeinbergSMInterface.ModelSector a ≃ₗ[ℂ] Residual a :=
  (WeinbergSMInterface.reducedEquiv a).trans (equiv a)

def comparison : Residual a ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (trivial ℂ R ℂ) :=
  LinearEquivComparison.comparison (onSMEquiv a) (WeinbergSMInterface.homEquiv a)

attribute [local irreducible] comparison

theorem extraction_commutes (f : WeinbergSMInterface.ModelSector a) :
    comparison a (onSMEquiv a f) = WeinbergSMInterface.homEquiv a f := by
  unfold comparison
  exact LinearEquivComparison.extraction (onSMEquiv a) (WeinbergSMInterface.homEquiv a) f

theorem reconstruction_commutes (q : Residual a) :
    (onSMEquiv a).symm q = (WeinbergSMInterface.homEquiv a).symm (comparison a q) := by
  unfold comparison
  exact LinearEquivComparison.reconstruction (onSMEquiv a) (WeinbergSMInterface.homEquiv a) q

theorem reconstruct_extract (f : WeinbergSMInterface.ModelSector a) :
    (onSMEquiv a).symm (onSMEquiv a f) = f := LinearEquivComparison.inverse_left (onSMEquiv a) f
theorem extract_reconstruct (q : Residual a) :
    onSMEquiv a ((onSMEquiv a).symm q) = q := LinearEquivComparison.inverse_right (onSMEquiv a) q

theorem forbidden_iff : (∀ f : WeinbergSMInterface.ModelSector a, f = 0) ↔
    ∀ q : Residual a, q = 0 := by
  exact LinearEquivComparison.forbidden (onSMEquiv a)

theorem nonzero_iff : (∃ f : WeinbergSMInterface.ModelSector a, f ≠ 0) ↔
    ∃ q : Residual a, q ≠ 0 := by
  exact LinearEquivComparison.nonzero (onSMEquiv a)

def oneGenerationEquiv : Residual (trivial ℂ R ℂ) ≃ₗ[ℂ] ℂ :=
  (onSMEquiv (trivial ℂ R ℂ)).symm.trans (WeinbergSMInterface.oneGenerationEquiv (R := R))

end
end GUT.GradedWeinbergComparison
