import Physics.StandardModel.Gauge.Tensors.WeakContragredient
import Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport
import Math.RepresentationTheory.Tensors.InvariantPairing

/-! Explicit nonzero charged-fermion Yukawa gauge contractions. -/
namespace Physics.SMYukawaContractions
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance
abbrev higgs := twist weak 3
abbrev antiHiggs := higgs.dual

/-- Contract the two weak doublets, retaining the color vector. -/
def upLinear : (Quark ⊗[ℂ] Weak) →ₗ[ℂ] Color :=
  (TensorProduct.rid ℂ Color).toLinearMap.comp
    ((TensorProduct.map LinearMap.id weakTensor).comp
      (TensorProduct.assoc ℂ Color Weak Weak).toLinearMap)
@[simp] theorem upLinear_tmul (a : Color) (w h : Weak) :
    upLinear ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] h) = eps2 w h • a := by simp [upLinear]

def upMap : IntertwiningMap (quark.tprod higgs) upRight where
  toLinearMap := upLinear
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v h
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add,TensorProduct.add_tmul,hv,hw]
    | tmul a w =>
      have hp : phase 1 g * phase 3 g = phase 4 g :=
        (HyperchargeTensorTransport.phase_add 1 3 g).symm
      change upLinear (((phase 1 g) • (color g a ⊗ₜ[ℂ] weak g w)) ⊗ₜ[ℂ]
        ((phase 3 g) • weak g h)) = phase 4 g • color g (upLinear ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] h))
      simp only [TensorProduct.smul_tmul',TensorProduct.tmul_smul,map_smul,upLinear_tmul,smul_smul]
      have he := eps2_invariant (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) g.2.1.prop.2 w h
      change eps2 (weak g w) (weak g h) = eps2 w h at he
      rw [he]
      congr 1
      calc
        _ = (phase 1 g * phase 3 g) * eps2 w h := by ring
        _ = _ := by rw [hp]

def upGauge : IntertwiningMap ((quark.tprod higgs).tprod upRight.dual)
    (trivial ℂ GaugeGroup ℂ) :=
  (InvariantPairing.evaluation upRight).comp (upMap.tensor (IntertwiningMap.id upRight.dual))

/-- Evaluate the Higgs covector on the quark's weak component. -/
def downLinear : (Quark ⊗[ℂ] Module.Dual ℂ Weak) →ₗ[ℂ] Color :=
  (TensorProduct.rid ℂ Color).toLinearMap.comp
    ((TensorProduct.map LinearMap.id (contractRight ℂ Weak)).comp
      (TensorProduct.assoc ℂ Color Weak (Module.Dual ℂ Weak)).toLinearMap)
@[simp] theorem downLinear_tmul (a : Color) (w : Weak) (h : Module.Dual ℂ Weak) :
    downLinear ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] h) = h w • a := by simp [downLinear]

def downMap : IntertwiningMap (quark.tprod antiHiggs) downRight where
  toLinearMap := downLinear
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v h
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add,TensorProduct.add_tmul,hv,hw]
    | tmul a w =>
      have hp : phase 1 g * phase 3 g⁻¹ = phase (-2) g := by
        rw [HyperchargeTensorTransport.phase_inv]
        exact (HyperchargeTensorTransport.phase_add 1 (-3) g).symm
      have hw : weak g⁻¹ (weak g w) = w := by simp
      change downLinear (((phase 1 g) • (color g a ⊗ₜ[ℂ] weak g w)) ⊗ₜ[ℂ]
        (higgs.dual g h)) = phase (-2) g • color g (downLinear ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] h))
      simp only [TensorProduct.smul_tmul',map_smul,downLinear_tmul]
      change (h (higgs g⁻¹ (weak g w))) • (phase 1 g • color g a) = _
      rw [show higgs g⁻¹ (weak g w) = phase 3 g⁻¹ • w from by
        change phase 3 g⁻¹ • weak g⁻¹ (weak g w) = _; rw [hw]]
      rw [map_smul]
      simp only [smul_smul]
      congr 1
      calc
        _ = (phase 1 g * phase 3 g⁻¹) * h w := by ring
        _ = _ := by rw [hp]

def downGauge : IntertwiningMap ((quark.tprod antiHiggs).tprod downRight.dual)
    (trivial ℂ GaugeGroup ℂ) :=
  (InvariantPairing.evaluation downRight).comp (downMap.tensor (IntertwiningMap.id downRight.dual))

/-- Hypercharges -3 and -3 combine into the right-electron line -6. -/
def electronMap : IntertwiningMap (lepton.tprod antiHiggs) electronRight where
  toLinearMap := contractRight ℂ Weak
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro w h
    have hp : phase (-3) g * phase 3 g⁻¹ = phase (-6) g := by
      rw [HyperchargeTensorTransport.phase_inv]
      exact (HyperchargeTensorTransport.phase_add (-3) (-3) g).symm
    change (higgs.dual g h) (lepton g w) = phase (-6) g • h w
    change h (higgs g⁻¹ (lepton g w)) = _
    have hw : weak g⁻¹ (weak g w) = w := by simp
    change h (phase 3 g⁻¹ • weak g⁻¹ (phase (-3) g • weak g w)) = _
    simp only [map_smul,hw,smul_smul]
    rw [mul_comm,hp]

def electronGauge : IntertwiningMap ((lepton.tprod antiHiggs).tprod electronRight.dual)
    (trivial ℂ GaugeGroup ℂ) :=
  (InvariantPairing.evaluation electronRight).comp
    (electronMap.tensor (IntertwiningMap.id electronRight.dual))

def colorCovector : Module.Dual ℂ Color := LinearMap.proj 0
def weakCovector : Module.Dual ℂ Weak := LinearMap.proj 0
def lineCovector : Module.Dual ℂ ℂ := LinearMap.id

theorem up_witness : upGauge (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] colorCovector) = 1 := by
  norm_num [upGauge,IntertwiningMap.comp_apply,upMap,InvariantPairing.evaluation,
    upLinear_tmul,colorCovector,colorBasis,weakBasis,eps2]
theorem down_witness : downGauge (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakCovector) ⊗ₜ[ℂ] colorCovector) = 1 := by
  simp [downGauge,IntertwiningMap.comp_apply,downMap,InvariantPairing.evaluation,
    downLinear_tmul,colorCovector,weakCovector,colorBasis,weakBasis]
theorem electron_witness : electronGauge ((weakBasis 0 ⊗ₜ[ℂ] weakCovector) ⊗ₜ[ℂ] lineCovector) = 1 := by
  simp [electronGauge,IntertwiningMap.comp_apply,electronMap,InvariantPairing.evaluation,
    weakCovector,lineCovector,weakBasis]
section Ordering
variable {A B S : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup S] [Module ℂ S]
  (a : Representation ℂ GaugeGroup A) (b : Representation ℂ GaugeGroup B)
  (s : Representation ℂ GaugeGroup S)
def swapLast : Equiv ((a.tprod b).tprod s) ((a.tprod s).tprod b) :=
  (Representation.TensorProduct.assoc a b s).trans
    ((Math.ExternalInvariantTensor.tensorEquiv (Representation.Equiv.refl a)
      (Representation.TensorProduct.comm b s)).trans
        (Representation.TensorProduct.assoc a s b).symm)
end Ordering

def upOrdered := upGauge.comp (swapLast quark upRight.dual higgs).toIntertwiningMap
def downOrdered := downGauge.comp (swapLast quark downRight.dual antiHiggs).toIntertwiningMap
def electronOrdered := electronGauge.comp (swapLast lepton electronRight.dual antiHiggs).toIntertwiningMap

@[simp] theorem upOrdered_apply (v : Quark) (u : Module.Dual ℂ Color) (h : Weak) :
    upOrdered ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] h) = upGauge ((v ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] u) := rfl
@[simp] theorem downOrdered_apply (v : Quark) (d : Module.Dual ℂ Color) (h : Module.Dual ℂ Weak) :
    downOrdered ((v ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] h) = downGauge ((v ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] d) := rfl
@[simp] theorem electronOrdered_apply (v : Weak) (e : Module.Dual ℂ ℂ) (h : Module.Dual ℂ Weak) :
    electronOrdered ((v ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] h) = electronGauge ((v ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] e) := rfl
end
end Physics.SMYukawaContractions
