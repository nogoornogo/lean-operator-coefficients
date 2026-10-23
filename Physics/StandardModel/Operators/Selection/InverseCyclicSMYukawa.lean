import Physics.StandardModel.Spectrum.Representations.InverseCyclicSMRealization
import Physics.StandardModel.Gauge.Tensors.SMYukawaContractions
import Physics.FieldTheory.Yukawa.Mass.SpinorYukawaContraction

/-! Actual nonzero Yukawa exterior coefficients for the constructed candidate. -/
namespace Physics.InverseCyclicSMYukawa
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor StandardSMGaugeTensor
open InverseCyclicSMRealization
open scoped TensorProduct

abbrev copy (c : ZMod 2) := InverseLeptonParitySelection.copies (V := Flavor) c
abbrev scalarCopy := trivial ℂ H ℂ

def flavorLinear : (Flavor ⊗[ℂ] Flavor) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (LinearMap.proj 0) (LinearMap.proj 0))
@[simp] theorem flavorLinear_apply (x y : Flavor) :
    flavorLinear (x ⊗ₜ[ℂ] y) = x 0 * y 0 := rfl

def flavorPair (c : ZMod 2) : IntertwiningMap ((copy c).tprod (copy c)) scalarCopy where
  toLinearMap := flavorLinear
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change flavorLinear ((ZMod.stdAddChar (c*g.toAdd) • x) ⊗ₜ[ℂ]
      (ZMod.stdAddChar (c*g.toAdd) • y)) = flavorLinear (x ⊗ₜ[ℂ] y)
    have hc : c+c = 0 := (show ∀ c : ZMod 2, c+c=0 from by decide +kernel) c
    have hh : ZMod.stdAddChar (c*g.toAdd) * ZMod.stdAddChar (c*g.toAdd) = 1 := by
      rw [← AddChar.map_add_eq_mul, ← add_mul,hc,zero_mul]
      simp
    simp only [TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
    rw [hh,one_smul]

def flavorTriple (c : ZMod 2) :=
  (Representation.TensorProduct.rid ℂ scalarCopy).toIntertwiningMap.comp
    ((flavorPair c).tensor (IntertwiningMap.id scalarCopy))

section Construct
variable {A B S : Type} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup S] [Module ℂ S]
  (a : Representation ℂ GaugeGroup A) (b : Representation ℂ GaugeGroup B)
  (s : Representation ℂ GaugeGroup S)

def regroup (c : ZMod 2) : Equiv
    (((external a (copy c)).tprod (external b (copy c))).tprod (external s scalarCopy))
    (external ((a.tprod b).tprod s) (((copy c).tprod (copy c)).tprod scalarCopy)) :=
  (tensorEquiv (regroupPair a b (copy c) (copy c)) (Representation.Equiv.refl _)).trans
    (regroupPair (a.tprod b) s ((copy c).tprod (copy c)) scalarCopy)

def internal (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ GaugeGroup ℂ))
    (c : ZMod 2) :=
  (coefficient f (flavorTriple c)).comp (regroup a b s c).toIntertwiningMap

@[simp] theorem internal_apply
    (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ GaugeGroup ℂ))
    (c : ZMod 2) (v : A) (w : B) (h : S) (x y : Flavor) (z : ℂ) :
    internal a b s f c (((v ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] z)) =
      f ((v ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] h) * (x 0 * y 0 * z) := by
  simp [internal,regroup,Representation.Equiv.trans,tensorEquiv,regroupPair,
    coefficient,flavorTriple,flavorPair,flavorLinear,mul_comm]
end Construct

abbrev higgs := external SMYukawaContractions.higgs scalarCopy
abbrev antiHiggs := external SMYukawaContractions.antiHiggs scalarCopy
abbrev upInternal := internal quark upRight.dual SMYukawaContractions.higgs SMYukawaContractions.upOrdered 0
abbrev downInternal := internal quark downRight.dual SMYukawaContractions.antiHiggs SMYukawaContractions.downOrdered 0
abbrev electronInternal := internal lepton electronRight.dual SMYukawaContractions.antiHiggs SMYukawaContractions.electronOrdered 1

/-- These definitions are typed on the actual light species, not an unrelated
charge-only model. Left Weyl spin is inserted before exterior descent. -/
def up : IntertwiningMap
    (((external (species 0) WeylSpinor.left).prod (external (species 1) WeylSpinor.left)).exteriorPower 2)
    (Representation.dual (higgs.comp (MonoidHom.fst G WeylSpinor.Group))) :=
  SpinorYukawaContraction.exterior (species 0) (species 1) higgs upInternal

def down : IntertwiningMap
    (((external (species 0) WeylSpinor.left).prod (external (species 2) WeylSpinor.left)).exteriorPower 2)
    (Representation.dual (antiHiggs.comp (MonoidHom.fst G WeylSpinor.Group))) :=
  SpinorYukawaContraction.exterior (species 0) (species 2) antiHiggs downInternal

def electron : IntertwiningMap
    (((external (species 3) WeylSpinor.left).prod (external (species 4) WeylSpinor.left)).exteriorPower 2)
    (Representation.dual (antiHiggs.comp (MonoidHom.fst G WeylSpinor.Group))) :=
  SpinorYukawaContraction.exterior (species 3) (species 4) antiHiggs electronInternal

abbrev firstFlavor : Flavor := Pi.single 0 1

theorem up_nonzero : up ≠ 0 := by
  apply SpinorYukawaContraction.exterior_nonzero _ _ _ upInternal
    ((SMEpsilonTensor.colorBasis 0 ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 0) ⊗ₜ[ℂ] firstFlavor)
    (SMYukawaContractions.colorCovector ⊗ₜ[ℂ] firstFlavor) (SMEpsilonTensor.weakBasis 1 ⊗ₜ[ℂ] (1 : ℂ))
  simp only [internal_apply,SMYukawaContractions.upOrdered_apply,SMYukawaContractions.up_witness]
  norm_num [firstFlavor]

theorem down_nonzero : down ≠ 0 := by
  apply SpinorYukawaContraction.exterior_nonzero _ _ _ downInternal
    ((SMEpsilonTensor.colorBasis 0 ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 0) ⊗ₜ[ℂ] firstFlavor)
    (SMYukawaContractions.colorCovector ⊗ₜ[ℂ] firstFlavor) (SMYukawaContractions.weakCovector ⊗ₜ[ℂ] (1 : ℂ))
  simp only [internal_apply,SMYukawaContractions.downOrdered_apply,SMYukawaContractions.down_witness]
  norm_num [firstFlavor]

theorem electron_nonzero : electron ≠ 0 := by
  apply SpinorYukawaContraction.exterior_nonzero _ _ _ electronInternal
    (SMEpsilonTensor.weakBasis 0 ⊗ₜ[ℂ] firstFlavor)
    (SMYukawaContractions.lineCovector ⊗ₜ[ℂ] firstFlavor) (SMYukawaContractions.weakCovector ⊗ₜ[ℂ] (1 : ℂ))
  simp only [internal_apply,SMYukawaContractions.electronOrdered_apply,SMYukawaContractions.electron_witness]
  norm_num [firstFlavor]
/-- One simultaneous certificate on the same named constructed input. -/
theorem construction_certificate :
    InverseCyclicSMCharges.YukawaNeutral (InverseCyclicSMCharges.chiral (0 : ZMod 2) 1) ∧
    ((0,1) : ZMod 2 × ZMod 2) ∈ InverseCyclicSMCharges.candidates 2 ∧
    Nonempty (Equiv mass.radical.toRepresentation light) ∧
    mass.form ≠ 0 ∧ up ≠ 0 ∧ down ≠ 0 ∧ electron ≠ 0 ∧
    (∀ n m, ∀ f : ComposableBLSupport.Input fermionFlavor higgsFlavor
      InverseLeptonParitySelection.target n m, f = 0) :=
  ⟨by unfold InverseCyclicSMCharges.YukawaNeutral InverseCyclicSMCharges.chiral; decide +kernel,
    InverseCyclicSMCharges.selected_candidate, ⟨radicalEquiv⟩,
    spectator_mass_nonzero,up_nonzero,down_nonzero,electron_nonzero,all_B1_forbidden⟩
end
end Physics.InverseCyclicSMYukawa
