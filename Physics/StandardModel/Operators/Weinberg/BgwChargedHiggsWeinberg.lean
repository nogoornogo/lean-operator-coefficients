import Physics.StandardModel.Operators.Selection.BgwZ6Selection
import Physics.StandardModel.Operators.Weinberg.WeinbergSMInterface

namespace Physics.BgwChargedHiggsWeinberg
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
abbrev H := CyclicCharge.Group 6
@[reducible] local instance : AddCommGroup (SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup (WeinbergModelSector.Lepton ℂ) := inferInstance
@[reducible] local instance : AddCommGroup (BnvMixedInput.ScalarField (S := fun _ => ℂ) 0) := inferInstance
@[reducible] local instance : AddCommGroup
    ((⋀[ℂ]^2 (WeinbergModelSector.Lepton ℂ)) ⊗[ℂ]
      Sym[ℂ]^2 (BnvMixedInput.ScalarField (S := fun _ => ℂ) 0)) := inferInstance
abbrev neutralFlavor := trivial ℂ H ℂ
abbrev actualL := DeltaLOneSignedFields.field (BgwZ6Selection.flavor (F := fun _ => ℂ)) 3
abbrev actualH := BnvMixedInput.scalarField (BgwZ6Selection.scalarFlavor (S := fun _ => ℂ)) 0
abbrev neutralL := DeltaLOneSignedFields.field (fun _ => neutralFlavor) 3
abbrev neutralH := BnvMixedInput.scalarField (fun _ => neutralFlavor) 0
def phase (q : ℤ) (g : WeinbergSMInterface.PhysicalGroup H) : ℂ :=
  MixedChargeSelection.cyclicCharacter g.2 q

theorem lepton_scalar (g : WeinbergSMInterface.PhysicalGroup H)
    (x : DeltaLOneSignedFields.Field (F := fun _ => ℂ) 3) : actualL g x = phase 2 g • neutralL g x := by
  have he : actualL g = phase 2 g • neutralL g := by
    apply TensorProduct.ext'
    intro v w
    simp [actualL, DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField,
      DeltaLOneSignedFields.gauge, neutralL, DeltaLOneSignedFields.rightHanded, FourSameWeylCompleteness.action,
      BgwZ6Selection.flavor, BgwZ6Selection.copies, BgwZ6Selection.fq,
      ExternalInvariantTensor.external, Representation.tprod_apply, phase,
      MixedChargeSelection.cyclicCharacter, ← smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.map_tmul, LinearMap.smul_apply]
  exact LinearMap.congr_fun he x

theorem higgs_scalar (g : WeinbergSMInterface.PhysicalGroup H)
    (x : BnvMixedInput.ScalarField (S := fun _ => ℂ) 0) : actualH g x = phase 1 g • neutralH g x := by
  have he : actualH g = phase 1 g • neutralH g := by
    apply TensorProduct.ext'
    intro v w
    simp [actualH, BnvMixedInput.scalarField, BnvMixedInput.scalarGauge,
      neutralH, BgwZ6Selection.scalarFlavor,
      BgwZ6Selection.copies, BgwZ6Selection.bq, ExternalInvariantTensor.external,
      Representation.tprod_apply, phase, MixedChargeSelection.cyclicCharacter,
      ← smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.map_tmul, LinearMap.smul_apply]
  exact LinearMap.congr_fun he x

theorem phases (g : WeinbergSMInterface.PhysicalGroup H) :
    (phase 2 g * phase 2 g) * (phase 1 g * phase 1 g) = 1 := by
  let chi := MixedChargeSelection.cyclicCharacter g.2
  change (chi (2 : ZMod 6) * chi 2) * (chi 1 * chi 1) = 1
  rw [← chi.map_add_eq_mul, ← chi.map_add_eq_mul, ← chi.map_add_eq_mul]
  have hz : (2+2+(1+1) : ZMod 6) = 0 := by decide
  rw [hz]; exact chi.map_zero_eq_one

abbrev actualDomain := (actualL.exteriorPower 2).tprod (actualH.symmetricPower 2)
abbrev neutralDomain := (neutralL.exteriorPower 2).tprod (neutralH.symmetricPower 2)

def neutralEquiv : Representation.Equiv actualDomain neutralDomain where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 2) (BnvMixedInput.ScalarField (S := fun _ => ℂ) 0))
    rintro _ ⟨h,rfl⟩
    change ((actualL.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 x)) ⊗ₜ[ℂ]
      ((actualH.symmetricPower 2) g (SymmetricPower.tprod ℂ h)) =
      ((neutralL.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 x)) ⊗ₜ[ℂ]
      ((neutralH.symmetricPower 2) g (SymmetricPower.tprod ℂ h))
    rw [Representation.exteriorPower_apply_ιMulti, Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, Representation.symmetricPower_apply_tprod]
    simp only [Function.comp_def, higgs_scalar]
    have hl : (fun i => actualL g (x i)) = (fun i => phase 2 g • neutralL g (x i)) := by
      funext i
      exact lepton_scalar g (x i)
    rw [hl]
    rw [(exteriorPower.ιMulti ℂ 2).map_smul_univ, (SymmetricPower.tprod ℂ).map_smul_univ]
    simp only [Fin.prod_univ_two]
    rw [TensorProduct.smul_tmul_smul, phases, one_smul]

def higgsEquiv : Representation.Equiv neutralH (WeinbergSMInterface.higgs (R := H)) where
  toLinearEquiv := TensorProduct.rid ℂ (BnvMixedInput.ScalarGaugeCarrier 0)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x z
    change z • ((WeinbergSMInterface.higgs (R := H)) g x) =
      (WeinbergSMInterface.higgs (R := H)) g (z • x)
    exact ((WeinbergSMInterface.higgs (R := H)) g).map_smul z x |>.symm

def leptonEquiv : Representation.Equiv neutralL (WeinbergSMInterface.lepton neutralFlavor) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x u
    simp [neutralL, DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField,
      DeltaLOneSignedFields.gauge, DeltaLOneSignedFields.rightHanded, FourSameWeylCompleteness.action,
      WeinbergSMInterface.lepton, ExternalInvariantTensor.external, Representation.tprod_apply]

def domainEquiv : Representation.Equiv actualDomain (WeinbergSMInterface.domain neutralFlavor) :=
  neutralEquiv.trans (ExternalInvariantTensor.tensorEquiv
    (leptonEquiv.exteriorPower 2) (higgsEquiv.symmetricPower 2))

abbrev Sector := IntertwiningMap actualDomain (trivial ℂ (WeinbergSMInterface.PhysicalGroup H) ℂ)
def coefficientEquiv : Sector ≃ₗ[ℂ] ℂ :=
  (InvariantCoefficientTransport.alongEquiv domainEquiv).trans
    (WeinbergSMInterface.oneGenerationEquiv (R := H))

def witness : Sector := coefficientEquiv.symm 1
theorem witness_coordinate : coefficientEquiv witness = 1 :=
  coefficientEquiv.apply_symm_apply 1

theorem witness_nonzero : witness ≠ 0 := by
  intro h
  have he := congrArg coefficientEquiv h
  simp [witness] at he
theorem exists_nonzero : ∃ f : Sector, f ≠ 0 := ⟨witness, witness_nonzero⟩

end
end Physics.BgwChargedHiggsWeinberg
