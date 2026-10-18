import GUT.SU5.SelectionRules.ActualFullFamilyIndex
import Physics.StandardModel.Operators.StandardGaugeQqueExterior
import Math.RepresentationTheory.Unitary.UnitarySubrepresentationOrthogonality

namespace GUT.SU5.ActualFullFamilyQque
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding StandardSMGaugeTensor
open InvariantWeylMass InvariantMassNormalForm ActualFullFamilyIndex
open SplitRepresentationProjection
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup FortyHyperchargeExclusion.Kernel := inferInstance
local instance : Module ℂ FortyHyperchargeExclusion.Kernel := inferInstance
local instance : AddCommGroup ExoticHyperchargeBasis.Fifty := inferInstance
local instance : Module ℂ ExoticHyperchargeBasis.Fifty := inferInstance

def qGeneration : IntertwiningMap quark smGeneration :=
  (IntertwiningMap.inl ℂ (ten.comp hom) (antifundamental.comp hom)).comp
    (ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp quarkI)
def uGeneration : IntertwiningMap upRight.dual smGeneration :=
  (IntertwiningMap.inl ℂ (ten.comp hom) (antifundamental.comp hom)).comp
    (ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp upI)
def eGeneration : IntertwiningMap electronRight.dual smGeneration :=
  (IntertwiningMap.inl ℂ (ten.comp hom) (antifundamental.comp hom)).comp
    (ExteriorSquareBranching.tenEquiv.symm.toIntertwiningMap.comp electronI)

theorem qGeneration_injective : Function.Injective qGeneration := by
  intro x y h
  have he := congrArg (fun v : Ten × BarFive => ExteriorSquareBranching.tenEquiv v.1) h
  change ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (quarkI x)) =
    ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (quarkI y)) at he
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply] at he
  exact congrArg (fun v => v.2.1) he
theorem uGeneration_injective : Function.Injective uGeneration := by
  intro x y h
  have he := congrArg (fun v : Ten × BarFive => ExteriorSquareBranching.tenEquiv v.1) h
  change ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (upI x)) =
    ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (upI y)) at he
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply] at he
  exact congrArg Prod.fst he
theorem eGeneration_injective : Function.Injective eGeneration := by
  intro x y h
  have he := congrArg (fun v : Ten × BarFive => ExteriorSquareBranching.tenEquiv v.1) h
  change ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (electronI x)) =
    ExteriorSquareBranching.tenEquiv (ExteriorSquareBranching.tenEquiv.symm (electronI y)) at he
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply] at he
  exact congrArg (fun v => v.2.2) he

variable {F : Type} [AddCommGroup F] [Module ℂ F] (rho : Representation ℂ GaugeGroup F)

/-- All three left-chiral participating species are actual invariant subspaces
of the unchanged light radical. Right-handed fields use the dual subspaces. -/
structure LightTriplet where
  Q : Subrepresentation rho
  UC : Subrepresentation rho
  EC : Subrepresentation rho
  qEquiv : Representation.Equiv Q.toRepresentation quark
  uEquiv : Representation.Equiv UC.toRepresentation upRight.dual
  eEquiv : Representation.Equiv EC.toRepresentation electronRight.dual

namespace LightTriplet
def HasCoefficient (X : LightTriplet rho) : Prop :=
  PhysicalQqueEndpoint.HasExterior X.Q.toRepresentation X.UC.toRepresentation.dual X.EC.toRepresentation.dual
theorem hasCoefficient (X : LightTriplet rho) : X.HasCoefficient :=
  StandardGaugeQqueExterior.on_fields _ _ _ X.qEquiv
    ((dualEquiv X.uEquiv).trans (bidualEquiv upRight).symm)
    ((dualEquiv X.eEquiv).trans (bidualEquiv electronRight).symm)
end LightTriplet

def selectCopy {V : Type} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (N : ℕ) (i : Fin N)
    (e : Representation.Equiv rho (FiniteSpectrum.copies N smGeneration))
    (f : IntertwiningMap r smGeneration) : IntertwiningMap r rho :=
  e.symm.toIntertwiningMap.comp ((BipartiteNormalForm.copySlot N smGeneration i).comp f)

theorem selectCopy_injective {V : Type} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (N : ℕ) (i : Fin N)
    (e : Representation.Equiv rho (FiniteSpectrum.copies N smGeneration))
    (f : IntertwiningMap r smGeneration) (hf : Function.Injective f) :
    Function.Injective (selectCopy rho r N i e f) := by
  intro x y h
  have he := congrArg (fun v : F => e v i) h
  change (e (e.symm (Pi.single i (f x)))) i = (e (e.symm (Pi.single i (f y)))) i at he
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply] at he
  apply hf
  simpa using he

def tripletOfExactSM (N : ℕ) (hN : 0<N)
    (e : Representation.Equiv rho (FiniteSpectrum.copies N smGeneration)) : LightTriplet rho := by
  let i : Fin N := ⟨0,hN⟩
  let fq := selectCopy rho quark N i e qGeneration
  let fu := selectCopy rho upRight.dual N i e uGeneration
  let fe := selectCopy rho electronRight.dual N i e eGeneration
  exact ⟨fq.range, fu.range, fe.range,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fq
      (selectCopy_injective rho quark N i e qGeneration qGeneration_injective)).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fu
      (selectCopy_injective rho upRight.dual N i e uGeneration uGeneration_injective)).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fe
      (selectCopy_injective rho electronRight.dual N i e eGeneration eGeneration_injective)).symm⟩

/-- This prohibition predicate covers every admitted SM species subspace of the
actual light representation. Its negation is not a generated coupling claim. -/
def ForbidsEveryLightQque : Prop := ∀ X : LightTriplet rho, ¬ X.HasCoefficient

theorem exact_sm_not_forbidden (N : ℕ) (hN : 0<N)
    (e : Representation.Equiv rho (FiniteSpectrum.copies N smGeneration)) :
    ¬ ForbidsEveryLightQque rho := by
  intro h
  let X := tripletOfExactSM rho N hN e
  exact h X X.hasCoefficient

theorem full_family_exclusion (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ) (hN : 0<N)
    (e : Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) :
    ((p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3) ∧
      ¬ ForbidsEveryLightQque B.radical.toRepresentation :=
  ⟨net_constraints_of_exact_sm p q B N e, exact_sm_not_forbidden _ N hN e⟩

theorem no_sm_prohibiting_input (p q : Counts) (B : SymmetricMass (fields p q)) :
    ¬ ∃ N : ℕ, 0<N ∧
      Nonempty (Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) ∧
      ForbidsEveryLightQque B.radical.toRepresentation := by
  rintro ⟨N,hN,⟨e⟩,hf⟩
  exact exact_sm_not_forbidden _ N hN e hf
end
end GUT.SU5.ActualFullFamilyQque
