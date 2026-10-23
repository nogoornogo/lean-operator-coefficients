import GUT.SU6.Boundary.Protection
import Physics.FieldTheory.Fields.SelectedFields
import Math.RepresentationTheory.Fields.DerivativeConnection
import Math.RepresentationTheory.Fields.JetConnection

/-! The boundary dictionary is constructed from the existing component maps
for the actual SM gauge and residual circle actions together. -/
namespace GUT.SU6BoundaryFieldConnection
set_option autoImplicit false
noncomputable section
open Math Physics Representation StandardSMGaugeTensor SMEpsilonTensor StandardSMExterior
open SU6BoundarySelection SU6BoundaryBaryon
open scoped TensorProduct

def residualBlocks : Representation ℂ Circle Blocks :=
  algebraicEquiv.toLinearEquiv.conjRingEquiv.toMonoidHom.comp (defining.exteriorPower 2)

theorem residualBlocks_apply (z : Circle) (u : Blocks) :
    residualBlocks z u = blocksAction z u := by
  change branch (defining.exteriorPower 2 z (algebraicEquiv.symm u)) = _
  rw [branch_action]
  change blocksAction z (algebraicEquiv (algebraicEquiv.symm u)) = _
  rw [Representation.Equiv.apply_symm_apply]

theorem actions_commute (g : GaugeGroup) (z : Circle) (u : Blocks) :
    blocksRho g (residualBlocks z u) = residualBlocks z (blocksRho g u) := by
  rw [residualBlocks_apply, residualBlocks_apply]
  change blocksRho g (StandardScalarBlock.blocks ((z : ℂ)^2) 1 1 u) =
    StandardScalarBlock.blocks ((z : ℂ)^2) 1 1 (blocksRho g u)
  simp [blocksRho, StandardScalarBlock.blocks, Representation.prod]

def ambient := CommutingActionHom.action blocksRho residualBlocks actions_commute

def selected : Subrepresentation ambient where
  toSubmodule := fifteen.selected
  apply_mem_toSubmodule g u hu := by
    apply fifteen.preserved (blocksRho g.1) (fifteen_gauge_uv g.1) (fifteen_gauge_ir g.1)
    change residualBlocks g.2 u ∈ fifteen.selected
    rw [residualBlocks_apply]
    exact fifteen.preserved (blocksAction g.2) (boundaries15 g.2).1 (boundaries15 g.2).2 hu

def phase : Representation ℂ Circle Light15 where
  toFun z :=
    { toFun := fun u => ((z : ℂ)^2 • u.1, u.2)
      map_add' _ _ := by simp [smul_add]
      map_smul' _ _ := by simp [smul_smul, mul_comm] }
  map_one' := by ext u <;> simp
  map_mul' z w := by ext u <;> simp [mul_pow, smul_smul]

theorem target_commute (g : GaugeGroup) (z : Circle) (u : Light15) :
    (quark.prod electronRight.dual) g (phase z u) =
      phase z ((quark.prod electronRight.dual) g u) := by
  change (quark g ((z : ℂ)^2 • u.1), electronRight.dual g u.2) = _
  rw [map_smul]
  rfl

def target := CommutingActionHom.action (quark.prod electronRight.dual) phase target_commute

def embed : IntertwiningMap target ambient where
  toLinearMap := embed15
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    change embed15 ((quark.prod electronRight.dual) g.1 (phase g.2 u)) =
      blocksRho g.1 (residualBlocks g.2 (embed15 u))
    rw [residualBlocks_apply, left15_charges, embed15_covariant]
    rfl

def dictionary : Representation.Equiv target selected.toRepresentation :=
  FieldSelection.ofMaps selected embed extract15
    (fun u => (left15_exact _).mpr (by change embed15 (extract15 (embed15 u)) = embed15 u; rw [extract_embed15]))
    extract_embed15 (fun u hu => (left15_exact u).mp hu)

theorem extraction_covariant (g : GaugeGroup × Circle) (u : selected.toSubmodule) :
    extract15 (ambient g u) = target g (extract15 u) :=
  FieldSelection.extraction_covariant selected embed extract15
    (fun u => (left15_exact _).mpr (by change embed15 (extract15 (embed15 u)) = embed15 u; rw [extract_embed15]))
    extract_embed15 (fun u hu => (left15_exact u).mp hu) g u

theorem dictionary_agrees (u : Light15) : (dictionary u).val = (left15Equiv u).val := rfl

@[reducible] local instance : AddCommGroup selected.toSubmodule := inferInstance
@[reducible] local instance : Module ℂ selected.toSubmodule := inferInstance

def leftWeyl : Representation.Equiv
    (ExternalInvariantTensor.external target WeylSpinor.left)
    (ExternalInvariantTensor.external selected.toRepresentation WeylSpinor.left) :=
  SelectedFields.withWeyl false dictionary

def conjugateInternal : Representation.Equiv target.dual selected.toRepresentation.dual :=
  SelectedFields.internalDual dictionary

def derivativeDictionary {I : Type*}
    (d : Representation ℂ ((GaugeGroup × Circle) × WeylSpinor.Group) (JetDirections.Direction I)) :=
  FieldJetConnection.coordinateJets leftWeyl
    (Module.Free.chooseBasis ℂ _) (Module.Free.chooseBasis ℂ _) d

abbrev scalar := Representation.trivial ℂ (GaugeGroup × Circle) ℂ

def mixedInput (n m : ℕ) :
    InvariantCoefficientTransport.Invariants ((target.exteriorPower n).tprod (scalar.symmetricPower m)) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      ((selected.toRepresentation.exteriorPower n).tprod (scalar.symmetricPower m)) :=
  FieldSelection.mixedCoefficients dictionary (Representation.Equiv.refl scalar) n m

theorem coefficient_evaluation (n m : ℕ)
    (q : InvariantCoefficientTransport.Invariants
      ((target.exteriorPower n).tprod
        ((Representation.trivial ℂ (GaugeGroup × Circle) ℂ).symmetricPower m)))
    (u : ⋀[ℂ]^n Light15) (v : Sym[ℂ]^m ℂ) :
    mixedInput n m q (dictionary.exteriorPower n u ⊗ₜ[ℂ] v) = q (u ⊗ₜ[ℂ] v) := by
  simpa only [mixedInput, Representation.Equiv.symmetricPower_refl, Representation.Equiv.refl_apply] using
    FieldSelection.mixed_evaluation dictionary (Representation.Equiv.refl scalar) n m q u v

/-- Generic pairing replaces the old Circle-specific proof on the same maps. -/
theorem boundary_pairing (z : Circle) (a : ℂ)
    (f : Module.Dual ℂ SU6BoundaryCube.Cube) (u : SU6BoundaryCube.Square) :
    (defining.exteriorPower 3).dual z f
      (SU6BoundaryInteractions.join a (defining.exteriorPower 2 z u)) =
      f (SU6BoundaryInteractions.join a u) :=
  FieldSelection.dual_pairing
    { toLinearMap := SU6BoundaryInteractions.join a
      isIntertwining' g := LinearMap.ext (SU6BoundaryInteractions.join_covariant g a) } z f u

abbrev gaugeSix : Representation ℂ GaugeGroup SU6BoundaryCube.Vector :=
  FundamentalRepresentation.rho.comp StandardSMGroup.hom

theorem six_commute (g : GaugeGroup) (z : Circle) (u : SU6BoundaryCube.Vector) :
    gaugeSix g (defining z u) = defining z (gaugeSix g u) :=
  (LinearMap.congr_fun (defining_gauge_commutes z g) u).symm

def cubeAmbient := CommutingActionHom.action (gaugeSix.exteriorPower 3)
  (defining.exteriorPower 3) (FieldSelection.exterior_commute gaugeSix defining six_commute 3)

def colorPhase : Representation ℂ Circle Color where
  toFun z := (z : ℂ)^2 • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' z w := by apply LinearMap.ext; intro x; simp [mul_pow, smul_smul, mul_comm]

def upTarget := CommutingActionHom.action upRight colorPhase
  (fun g z u => map_smul (upRight g) ((z : ℂ)^2) u)

def embedUp : IntertwiningMap upTarget cubeAmbient where
  toLinearMap := SU6BoundaryCube.embed
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    change SU6BoundaryCube.embed (upRight g.1 ((g.2 : ℂ)^2 • u)) =
      exteriorPower.map 3 (FundamentalRepresentation.rho (StandardSMGroup.hom g.1))
        (defining.exteriorPower 3 g.2 (SU6BoundaryCube.embed u))
    rw [right20_charge, map_smul, map_smul, map_smul]
    exact congrArg (fun v => (g.2 : ℂ)^2 • v) (SU6BoundaryCube.embed_covariant g.1 u).symm

theorem up_image (u : Color) : embedUp u ∈ twenty.opposite.selected :=
  (right20_exact _).mpr (by
    change SU6BoundaryCube.embed (SU6BoundaryCube.contract (SU6BoundaryCube.embed u)) = _
    rw [SU6BoundaryCube.contract_embed]; rfl)

def upSelected := FieldSelection.realized embedUp SU6BoundaryCube.contract
  twenty.opposite.selected up_image (fun u hu => (right20_exact u).mp hu)

def upDictionary : Representation.Equiv upTarget upSelected.toRepresentation :=
  FieldSelection.ofMaps upSelected embedUp SU6BoundaryCube.contract up_image
    SU6BoundaryCube.contract_embed (fun u hu => (right20_exact u).mp hu)

@[reducible] local instance : AddCommGroup upSelected.toSubmodule := inferInstance
@[reducible] local instance : Module ℂ upSelected.toSubmodule := inferInstance

def upRightWeyl : Representation.Equiv
    (ExternalInvariantTensor.external upTarget WeylSpinor.right)
    (ExternalInvariantTensor.external upSelected.toRepresentation WeylSpinor.right) :=
  SelectedFields.withWeyl true upDictionary

def upDualLeftWeyl : Representation.Equiv
    (ExternalInvariantTensor.external upTarget.dual WeylSpinor.left)
    (ExternalInvariantTensor.external upSelected.toRepresentation.dual WeylSpinor.left) :=
  SelectedFields.withWeyl false (SelectedFields.internalDual upDictionary)

def sixAmbient := CommutingActionHom.action StandardSMGroup.heavy splitAction
  (by
    intro g z u
    change StandardSMGroup.heavy g ((z : ℂ)^2 • u.1, u.2) = _
    simp [StandardSMGroup.heavy, splitAction])

def downLeptonPhase : Representation ℂ Circle (Color × Weak) :=
  colorPhase.prod (Representation.trivial ℂ Circle Weak)

def downLeptonTarget := CommutingActionHom.action (downRight.prod (twist weak 3)) downLeptonPhase
  (by intro g z u; change (downRight g ((z : ℂ)^2 • u.1), _) = _; rw [map_smul]; rfl)

def embedDownLepton : IntertwiningMap downLeptonTarget sixAmbient where
  toLinearMap := embed6Right
  isIntertwining' g := by
    apply LinearMap.ext
    intro u
    change embed6Right ((downRight.prod (twist weak 3)) g.1 (downLeptonPhase g.2 u)) =
      StandardSMGroup.heavy g.1 (splitAction g.2 (embed6Right u))
    rw [SU6BoundaryProtection.right6_residual, right6_gauge]
    rfl

theorem downLepton_image (u : Color × Weak) : embedDownLepton u ∈ six.opposite.selected :=
  (right6_exact _).mpr rfl

theorem downLepton_reconstruct (u : Six) (hu : u ∈ six.opposite.selected) :
    embedDownLepton (extract6Right u) = u := by
  have h := (right6_exact u).mp hu
  change (u.1,(u.2.1,0)) = u
  rw [← h]

def downLeptonSelected := FieldSelection.realized embedDownLepton extract6Right
  six.opposite.selected downLepton_image downLepton_reconstruct

def downLeptonDictionary : Representation.Equiv downLeptonTarget downLeptonSelected.toRepresentation :=
  FieldSelection.ofMaps downLeptonSelected embedDownLepton extract6Right downLepton_image
    (fun _ => rfl) downLepton_reconstruct

/-- The physical lepton duality is reused, not inferred from a chirality label. -/
def leptonDual := SU6BoundaryProtection.lepton_dictionary

theorem sterile_neutral (g : GaugeGroup) (z : Circle) (a : ℂ) :
    StandardSMGroup.heavy g (splitAction z (0,(0,a))) = (0,(0,a)) := by
  simp [splitAction, StandardSMGroup.heavy]

def sterileEmbed : IntertwiningMap (Representation.trivial ℂ (GaugeGroup × Circle) ℂ) sixAmbient where
  toLinearMap := (LinearMap.inr ℂ Color (Weak × ℂ)).comp (LinearMap.inr ℂ Weak ℂ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    exact (sterile_neutral g.1 g.2 a).symm

def sterileExtract : Six →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ Weak ℂ).comp (LinearMap.snd ℂ Color (Weak × ℂ))

theorem sterile_image (a : ℂ) : sterileEmbed a ∈ six.selected :=
  (left6_exact _).mpr rfl

def sterileSelected := FieldSelection.realized sterileEmbed sterileExtract
  six.selected sterile_image (fun u hu => (left6_exact u).mp hu)

/-- This exact neutral amplitude is deliberately separate from the charged
SM dictionary and from the ten-species coefficient alphabet. -/
def sterileDictionary : Representation.Equiv
    (Representation.trivial ℂ (GaugeGroup × Circle) ℂ) sterileSelected.toRepresentation :=
  FieldSelection.ofMaps sterileSelected sterileEmbed sterileExtract sterile_image
    (fun _ => rfl) (fun u hu => (left6_exact u).mp hu)

def wedgeInteraction : IntertwiningMap (defining.tprod (defining.exteriorPower 2))
    (defining.exteriorPower 3) where
  toLinearMap := ExteriorCubeHook.multiply
  isIntertwining' z := by
    apply TensorProduct.ext'
    intro v w
    exact ExteriorCubeHook.multiply_natural (defining z) v w

def joinFromVacuum (a : ℂ) := FieldSelection.atVacuum wedgeInteraction
  (SU6BoundaryInteractions.vev a) (fun z => SU6BoundaryInteractions.vev_fixed z a)

theorem joinFromVacuum_agrees (a : ℂ) :
    (joinFromVacuum a).toLinearMap = SU6BoundaryInteractions.join a := rfl

end
end GUT.SU6BoundaryFieldConnection
