import Physics.StandardModel.Operators.Weinberg.WeinbergModelSector
import Physics.StandardModel.Operators.Weinberg.WeinbergScalarFlavor

open Math

/-! The actual SM covering-product group, including hypercharge cancellation,
and independently supplied field identifications for the LLHH sector. -/
namespace Physics.WeinbergSMInterface
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor WeinbergModelSector
open scoped TensorProduct
variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

@[reducible] local instance : AddCommGroup (Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup (Lepton F) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 (Lepton F)) ⊗[ℂ] Sym[ℂ]^2 Weak) := inferInstance

abbrev PhysicalGroup (R : Type*) := (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R

def projection : PhysicalGroup R →* ReducedGroup R where
  toFun g := ((g.1.1.2.1, g.1.2), g.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective (projection (R := R)) := by
  rintro ⟨⟨w,s⟩,r⟩
  exact ⟨((⟨1,w,1⟩,s),r), rfl⟩

def lepton : Representation ℂ (PhysicalGroup R) (Lepton F) :=
  external (external StandardSMGaugeTensor.lepton WeylSpinor.left) a

def higgs : Representation ℂ (PhysicalGroup R) Weak :=
  (StandardSMGaugeTensor.twist StandardSMGaugeTensor.weak 3).comp
    ((MonoidHom.fst _ _).comp (MonoidHom.fst _ R))

theorem lepton_apply (g : PhysicalGroup R) (x : Lepton F) :
    lepton a g x = StandardSMGaugeTensor.phase (-3) g.1.1 •
      WeinbergModelSector.lepton a (projection g) x := by
  have he : lepton a g = StandardSMGaugeTensor.phase (-3) g.1.1 •
      WeinbergModelSector.lepton a (projection g) := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro s
    apply LinearMap.ext; intro u
    change ((StandardSMGaugeTensor.phase (-3) g.1.1 •
      StandardSMGaugeTensor.weak g.1.1 w) ⊗ₜ[ℂ] WeylSpinor.left g.1.2 s) ⊗ₜ[ℂ] a g.2 u = _
    rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
    rfl
  exact LinearMap.congr_fun he x

theorem higgs_apply (g : PhysicalGroup R) (x : Weak) :
    higgs g x = StandardSMGaugeTensor.phase 3 g.1.1 •
      WeinbergModelSector.higgs (projection g) x := rfl

theorem phases (g : StandardSMGaugeTensor.GaugeGroup) :
    (StandardSMGaugeTensor.phase (-3) g * StandardSMGaugeTensor.phase (-3) g) *
      (StandardSMGaugeTensor.phase 3 g * StandardSMGaugeTensor.phase 3 g) = 1 := by
  have h : (g.2.2 ^ (-3 : ℤ) * g.2.2 ^ (-3 : ℤ)) *
      (g.2.2 ^ (3 : ℤ) * g.2.2 ^ (3 : ℤ)) = 1 := by group
  exact congrArg ((↑) : Circle → ℂ) h

def domain := ((lepton a).exteriorPower 2).tprod ((higgs (R := R)).symmetricPower 2)
abbrev ModelSector := IntertwiningMap (domain a) (Representation.trivial ℂ (PhysicalGroup R) ℂ)

def neutralEquiv : Representation.Equiv (domain a)
    ((((WeinbergModelSector.lepton a).exteriorPower 2).tprod
      ((WeinbergModelSector.higgs (R := R)).symmetricPower 2)).comp projection) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 2) Weak)
    rintro _ ⟨h, rfl⟩
    change ((lepton a).exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 x) ⊗ₜ[ℂ]
      ((higgs (R := R)).symmetricPower 2) g (SymmetricPower.tprod ℂ h) =
      ((WeinbergModelSector.lepton a).exteriorPower 2) (projection g)
        (exteriorPower.ιMulti ℂ 2 x) ⊗ₜ[ℂ]
      ((WeinbergModelSector.higgs (R := R)).symmetricPower 2) (projection g)
        (SymmetricPower.tprod ℂ h)
    rw [Representation.exteriorPower_apply_ιMulti, Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, Representation.symmetricPower_apply_tprod]
    simp only [Function.comp_def, lepton_apply, higgs_apply]
    rw [(exteriorPower.ιMulti ℂ 2).map_smul_univ, (SymmetricPower.tprod ℂ).map_smul_univ]
    simp only [Fin.prod_univ_two]
    rw [TensorProduct.smul_tmul_smul, phases, one_smul]

def reducedEquiv : ModelSector a ≃ₗ[ℂ] WeinbergModelSector.ModelSector a :=
  (InvariantCoefficientTransport.alongEquiv (neutralEquiv a)).trans
    (InvariantCoefficientTransport.alongSurjection
      (((WeinbergModelSector.lepton a).exteriorPower 2).tprod
        ((WeinbergModelSector.higgs (R := R)).symmetricPower 2))
      (projection (R := R)) projection_surjective)

def homEquiv : ModelSector a ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ) :=
  (reducedEquiv a).trans (WeinbergModelSector.homEquiv a)

def coefficientEquiv : ModelSector a ≃ₗ[ℂ] WeinbergResidualHom.sector a :=
  (reducedEquiv a).trans (WeinbergModelSector.sectorEquiv a)

theorem coefficientEquiv_apply (f : ModelSector a) (x y : Weak) (s t : WeylSpinor.Space)
    (u v : F) (h : Fin 2 → Weak) :
    (coefficientEquiv a f).val (WeinbergResidualHom.input x y h s t u v) =
      f (exteriorPower.ιMulti ℂ 2 ![(x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u, (y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v] ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ h) :=
  WeinbergModelSector.sectorEquiv_apply a (reducedEquiv a f) x y s t u v h

theorem exists_nonzero_iff : (∃ f : ModelSector a, f ≠ 0) ↔
    ∃ k : IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ), k ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨homEquiv a f, fun h => hf ((homEquiv a).injective (h.trans (map_zero _).symm))⟩
  · rintro ⟨k, hk⟩
    exact ⟨(homEquiv a).symm k, fun h =>
      hk ((homEquiv a).symm.injective (h.trans (map_zero _).symm))⟩

def oneGenerationEquiv : ModelSector (Representation.trivial ℂ R ℂ) ≃ₗ[ℂ] ℂ :=
  (coefficientEquiv _).trans WeinbergScalarFlavor.oneGenerationEquiv

theorem oneGeneration_finrank : Module.finrank ℂ
    (ModelSector (Representation.trivial ℂ R ℂ)) = 1 := by
  rw [oneGenerationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

def majoranaEquiv (v : ℂ) (hv : v ≠ 0) : ModelSector a ≃ₗ[ℂ]
    WeinbergMajorana.MassCoefficients a :=
  (coefficientEquiv a).trans (WeinbergMajorana.evaluationEquiv a v hv)

def mass (v : ℂ) (f : ModelSector a) : InvariantWeylMass.SymmetricMass a :=
  WeinbergMajorana.mass a v (coefficientEquiv a f)

/-- Actual exterior evaluation at two neutrino directions and a specified neutral VEV. -/
theorem mass_evaluation (v : ℂ) (f : ModelSector a) (u w : F) :
    f (exteriorPower.ιMulti ℂ 2
      ![(weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] u,
        (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] w] ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ ![WeinbergMajorana.vacuum v,WeinbergMajorana.vacuum v]) =
      (mass a v f).form u w := by
  rw [← coefficientEquiv_apply]
  exact WeinbergMajorana.evaluation_formula a v (coefficientEquiv a f) u w

theorem mass_nonzero_iff (v : ℂ) (hv : v ≠ 0) (f : ModelSector a) :
    (mass a v f).form ≠ 0 ↔ f ≠ 0 := by
  have hz : (mass a v f).form = 0 ↔ majoranaEquiv a v hv f = 0 := by
    constructor
    · intro h
      apply Subtype.ext
      apply IntertwiningMap.ext
      apply TensorProduct.ext'
      intro u w
      exact LinearMap.congr_fun (LinearMap.congr_fun h u) w
    · intro h
      have he := congrArg (fun k : WeinbergMajorana.MassCoefficients a =>
        TensorProduct.curry k.val.toLinearMap) h
      exact he
  exact not_congr (hz.trans (majoranaEquiv a v hv).map_eq_zero_iff)

@[simp] theorem mass_zero_vev (f : ModelSector a) : (mass a 0 f).form = 0 := by
  ext u w
  change (0 : ℂ) ^ 2 * _ = 0
  simp

section ActualFields
variable {L H : Type*} [AddCommGroup L] [Module ℂ L] [AddCommGroup H] [Module ℂ H]
  (l : Representation ℂ (PhysicalGroup R) L) (h : Representation ℂ (PhysicalGroup R) H)

abbrev Sector := IntertwiningMap ((l.exteriorPower 2).tprod (h.symmetricPower 2))
  (Representation.trivial ℂ (PhysicalGroup R) ℂ)

/-- These are field identifications, not a nonzero coefficient or a spanning hypothesis. -/
structure Inputs where
  leptonEquiv : Representation.Equiv l (lepton a)
  higgsEquiv : Representation.Equiv h (higgs (R := R))

def onFieldsModelEquiv (i : Inputs a l h) : Sector l h ≃ₗ[ℂ] ModelSector a :=
  InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (i.leptonEquiv.exteriorPower 2)
      (i.higgsEquiv.symmetricPower 2))

def onFieldsEquiv (i : Inputs a l h) : Sector l h ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ) :=
  (onFieldsModelEquiv a l h i).trans (homEquiv a)

def onFieldsMajoranaEquiv (i : Inputs a l h) (v : ℂ) (hv : v ≠ 0) :
    Sector l h ≃ₗ[ℂ] WeinbergMajorana.MassCoefficients a :=
  (onFieldsModelEquiv a l h i).trans (majoranaEquiv a v hv)

theorem exists_on_fields_iff (i : Inputs a l h) : (∃ f : Sector l h, f ≠ 0) ↔
    ∃ k : IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ), k ≠ 0 :=
  ConstrainedCompleteness.exists_nonzero_iff (onFieldsEquiv a l h i)

end ActualFields

end
end Physics.WeinbergSMInterface
