import Math.RepresentationTheory.Exterior.ConstantPatternExterior
import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel
import Physics.StandardModel.Operators.Weinberg.LiWeinbergCertificate

/-! Concrete LLHH coordinates transported to the actual statistical kernel. -/
namespace Physics.LLHHKernelRank
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeinbergModelSector.Lepton (Fin 3 → ℂ)) := inferInstance

def flavor (s : DeltaLOneSignedInput.Species) :
    Representation ℂ Unit (ThreeGenerationFermionBound.Flavor s) := trivial ℂ Unit _
def pattern (_ : Fin 2) : DeltaLOneSignedInput.Species := 3
abbrev a := trivial ℂ Unit (Fin 3 → ℂ)

def sourceEquiv : Representation.Equiv ((WeinbergSMInterface.lepton a).exteriorPower 2)
    (SMFiniteHiggsSupport.source flavor pattern) :=
  ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 3 2

def bosonEquiv : Representation.Equiv
    ((WeinbergSMInterface.higgs (R := Unit)).symmetricPower 2)
    (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := Unit))
      SMHiggsConstituents.character 2 2) := by
  change Representation.Equiv ((NeutralHiggsPowers.higgs (H := Unit)).symmetricPower 2) _
  rw [SMHiggsConstituents.higgs_eq]
  exact TwistedSU2ClebschGordan.leftPower _ _ 2

def fullEquiv : Representation.Equiv (WeinbergSMInterface.domain a)
    (SMWeylFiniteKernel.fullAction flavor pattern 2 2) :=
  ExternalInvariantTensor.tensorEquiv sourceEquiv bosonEquiv

def localEquiv : Representation.Equiv
    ((WeinbergSMInterface.domain a).comp (MonoidHom.inl SMIntegralLocalWeights.Group Unit))
    (SMIntegralLocalWeights.action flavor pattern 2 2) where
  toLinearEquiv := fullEquiv.toLinearEquiv
  isIntertwining' g := fullEquiv.isIntertwining' (g,1)

theorem inclusion_surjective : Function.Surjective
    (MonoidHom.inl SMIntegralLocalWeights.Group Unit) := by
  rintro ⟨g,u⟩
  exact ⟨g, by cases u; rfl⟩

def coefficientEquiv : InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor pattern 2 2) ≃ₗ[ℂ]
    WeinbergSMInterface.ModelSector a :=
  (InvariantCoefficientTransport.alongEquiv localEquiv.symm).trans
    (InvariantCoefficientTransport.alongSurjection (WeinbergSMInterface.domain a)
      (MonoidHom.inl _ Unit) inclusion_surjective)

def coordinates : InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor pattern 2 2) ≃ₗ[ℂ] (Sym (Fin 3) 2 → ℂ) :=
  coefficientEquiv.trans (LiWeinbergCertificate.flavorEquiv a (Pi.basisFun ℂ (Fin 3))
    LiWeinbergCertificate.trivial_symmetric_action)

def kernelCoordinates : SMFullLocalKernel.Kernel flavor pattern 2 2 ≃ₗ[ℂ]
    (Sym (Fin 3) 2 → ℂ) :=
  (SMFullLocalKernel.coefficientEquiv flavor pattern 2 2).symm.trans coordinates

/-- Explicit finite indices, with no choice of a basis by `Module.finBasis`. -/
def leptonBasis := (((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).tensorProduct
  (Pi.basisFun ℂ (Fin 3))).reindex
    (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).prodCongr (Equiv.refl (Fin 3))).trans
      finProdFinEquiv)

def carrierBasis := (((leptonBasis.exteriorPower 2).tensorProduct
  ((Pi.basisFun ℂ (Fin 2)).symmetricPower 2))).map fullEquiv.toLinearEquiv

def coefficientBasis := Module.Basis.ofEquivFun coordinates

theorem reconstruct_extract (f : InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor pattern 2 2)) :
    coordinates.symm (coordinates f) = f := coordinates.symm_apply_apply f

theorem extract_reconstruct (c : Sym (Fin 3) 2 → ℂ) :
    coordinates (coordinates.symm c) = c := coordinates.apply_symm_apply c

theorem kernel_dimension : Module.finrank ℂ (SMFullLocalKernel.Kernel flavor pattern 2 2) = 6 := by
  rw [kernelCoordinates.finrank_eq, Module.finrank_pi, Sym.card_sym_eq_choose]
  norm_num [Nat.choose_two_right]

theorem carrier_dimension : Module.finrank ℂ (SMFullLocalKernel.Carrier flavor pattern 2) = 198 := by
  rw [← fullEquiv.toLinearEquiv.finrank_eq]
  rw [Module.finrank_tensorProduct, exteriorPower.finrank_eq, SymmetricPower.finrank_eq]
  norm_num [WeinbergModelSector.Lepton, SMEpsilonTensor.Weak, WeylSpinor.Space,
    Module.finrank_tensorProduct, Nat.choose_two_right, Nat.multichoose]

theorem rank : Module.finrank ℂ
    (LinearMap.range (SMFullLocalKernel.constraints flavor pattern 2 2)) = 192 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (SMFullLocalKernel.constraints flavor pattern 2 2)
  have hk := kernel_dimension
  have hd := carrier_dimension
  change Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor pattern 2 2)) +
    Module.finrank ℂ (SMFullLocalKernel.Kernel flavor pattern 2 2) =
    Module.finrank ℂ (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor pattern 2)) → ℂ) at h
  simp only [Module.finrank_pi, Fintype.card_fin, hk, hd] at h
  omega

/-- Rank is unchanged by replacing the classical basis with explicit wedge indices. -/
theorem explicit_rank : Module.finrank ℂ (LinearMap.range
    (FiniteInvariantKernel.constraints (SMIntegralLocalWeights.action flavor pattern 2 2)
      carrierBasis (SMFullLocalKernel.tests 2))) = 192 := by
  let e := (FiniteInvariantKernel.equiv (SMIntegralLocalWeights.action flavor pattern 2 2)
    carrierBasis (SMFullLocalKernel.tests 2) (SMFullLocalKernel.exhaustive flavor pattern 2 2)).symm.trans
    coordinates
  have hk : Module.finrank ℂ (FiniteInvariantKernel.Kernel
      (SMIntegralLocalWeights.action flavor pattern 2 2) carrierBasis (SMFullLocalKernel.tests 2)) = 6 := by
    rw [e.finrank_eq, Module.finrank_pi, Sym.card_sym_eq_choose]
    norm_num [Nat.choose_two_right]
  have hd := Module.finrank_eq_card_basis carrierBasis
  rw [carrier_dimension] at hd
  have h := LinearMap.finrank_range_add_finrank_ker
    (FiniteInvariantKernel.constraints (SMIntegralLocalWeights.action flavor pattern 2 2)
      carrierBasis (SMFullLocalKernel.tests 2))
  rw [show Module.finrank ℂ (LinearMap.ker (FiniteInvariantKernel.constraints
    (SMIntegralLocalWeights.action flavor pattern 2 2) carrierBasis (SMFullLocalKernel.tests 2))) = 6
    from hk] at h
  simp only [Module.finrank_pi] at h
  omega

theorem rank_preserved : Module.finrank ℂ (LinearMap.range
    (FiniteInvariantKernel.constraints (SMIntegralLocalWeights.action flavor pattern 2 2)
      carrierBasis (SMFullLocalKernel.tests 2))) =
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor pattern 2 2)) :=
  explicit_rank.trans rank.symm

/-- The same statistical bridge retains any supplied residual flavor action. -/
def residualEquiv {H : Type*} [Group H]
    (f : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s)) :
    InvariantCoefficientTransport.Invariants (SMWeylFiniteKernel.fullAction f pattern 2 2) ≃ₗ[ℂ]
      IntertwiningMap ((f 3).symmetricPower 2) (trivial ℂ H ℂ) := by
  let eF : Representation.Equiv ((WeinbergSMInterface.lepton (f 3)).exteriorPower 2)
      (SMFiniteHiggsSupport.source f pattern) :=
    ConstantPatternExterior.equiv (DeltaLOneSignedFields.field f) 3 2
  let eB : Representation.Equiv ((WeinbergSMInterface.higgs (R := H)).symmetricPower 2)
      (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
        SMHiggsConstituents.character 2 2) := by
    change Representation.Equiv ((NeutralHiggsPowers.higgs (H := H)).symmetricPower 2) _
    rw [SMHiggsConstituents.higgs_eq]
    exact TwistedSU2ClebschGordan.leftPower _ _ 2
  exact (InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv eF eB).symm).trans (WeinbergSMInterface.homEquiv (f 3))

end
end Physics.LLHHKernelRank
