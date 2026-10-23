import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Physics.StandardModel.Gauge.Tensors.ResidualGaugeTensor

/-! Pointwise-neutral physical qque has a nonzero fermionic exterior
coefficient. No common residual constituent or UV-source premise is used. -/
namespace Physics.NeutralQqueExterior
set_option autoImplicit false
noncomputable section
open Math Representation SMEpsilonTensor StandardSMGaugeTensor
open FiniteAbelianChargeSectors StandardBranchProtonObstruction
open scoped TensorProduct

variable {H : Type*} [CommGroup H]
variable (k : Charges (Math.FiniteAbelianChargeSectors.ChargeLabel H))

local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup (Quark ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] WeylSpinor.Space) := inferInstance

abbrev q := StandardSMResidualTensor.charged quark k.quark.toMul
abbrev u := StandardSMResidualTensor.charged upRight (-k.up).toMul
abbrev e := StandardSMResidualTensor.charged electronRight (-k.electron).toMul

theorem charged_apply {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (chi : H →* Circle)
    (g : GaugeGroup × H) (x : V) :
    StandardSMResidualTensor.charged rho chi g x = (chi g.2 : ℂ) • rho g.1 x := rfl

theorem charged_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (chi : H →* Circle) :
    (StandardSMResidualTensor.charged rho chi).dual =
      StandardSMResidualTensor.charged rho.dual chi⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro v
  simp [StandardSMResidualTensor.charged, Representation.dual, map_smul]

def chargedEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ GaugeGroup V} {sigma : Representation ℂ GaugeGroup W}
    (eq : Representation.Equiv rho sigma) (chi : H →* Circle) :
    Representation.Equiv (StandardSMResidualTensor.charged rho chi)
      (StandardSMResidualTensor.charged sigma chi) :=
  Representation.Equiv.mk eq.toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    change eq ((chi g.2 : ℂ) • rho g.1 v) = (chi g.2 : ℂ) • sigma g.1 (eq v)
    rw [map_smul]
    exact congrArg (fun z => (chi g.2 : ℂ) • z)
      (Representation.IntertwiningMap.isIntertwining _ _ eq.toIntertwiningMap g.1 v))

def coefficient (hk : protonFirstCharacter k = 1) :
    QqueSpinorExterior.ExteriorCoefficient (q k) (u k) (e k) :=
  QqueSpinorExterior.exterior (q k) (u k) (e k)
    (StandardSMResidualTensor.qqueIntertwiner k hk)

def witness := exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
  (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) : Quark) ⊗ₜ[ℂ] weakBasis 0)
  (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) : Quark) ⊗ₜ[ℂ] weakBasis 1)
  (colorBasis 2 ⊗ₜ[ℂ] weakBasis 0)
  ((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1))

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_witness (hk : protonFirstCharacter k = 1) :
    coefficient k hk witness = 2 := by
  unfold coefficient QqueSpinorExterior.exterior
  rw [witness, FourSlotAlternation.coefficient_slots]
  rw [QqueSpinorExterior.ordered_apply (q k) (u k) (e k),
    QqueSpinorExterior.ordered_apply (q k) (u k) (e k)]
  simp only [StandardSMResidualTensor.qqueIntertwiner]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem coefficient_nonzero (hk : protonFirstCharacter k = 1) :
    coefficient k hk ≠ 0 := by
  intro hz
  have hw := coefficient_witness k hk
  rw [hz] at hw
  norm_num at hw

theorem has_nonzero_alternation (hk : protonFirstCharacter k = 1) :
    QqueSpinorExterior.HasNonzeroAlternation (q k) (u k) (e k) :=
  ⟨QqueSpinorExterior.ordered (q k) (u k) (e k)
    (StandardSMResidualTensor.qqueIntertwiner k hk), coefficient_nonzero k hk⟩

/-- Neutrality may be established using arbitrary pointwise factors;
only the physical species charges must be genuine characters. -/
theorem neutral_of_pointwise_block
    (a c w : H → Circle)
    (hQ : ∀ h, k.quark.toMul h = a h * c h * w h)
    (hU : ∀ h, k.up.toMul h = a h * c h * c h)
    (hE : ∀ h, k.electron.toMul h = a h * w h * w h) :
    protonFirstCharacter k = 1 := by
  apply MonoidHom.ext
  intro h
  simp only [protonFirstCharacter_apply, hQ, hU, hE, MonoidHom.one_apply]
  have hh : a h * c h * w h * (a h * c h * w h) =
      (a h * w h * w h) * (a h * c h * c h) := by ac_rfl
  rw [hh]
  group

theorem exists_of_pointwise_block
    (a c w : H → Circle)
    (hQ : ∀ h, k.quark.toMul h = a h * c h * w h)
    (hU : ∀ h, k.up.toMul h = a h * c h * c h)
    (hE : ∀ h, k.electron.toMul h = a h * w h * w h) :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient (q k) (u k) (e k), f ≠ 0 :=
  ⟨coefficient k (neutral_of_pointwise_block k a c w hQ hU hE),
    coefficient_nonzero k _⟩

set_option maxHeartbeats 800000 in
/-- Transport preserves the named qque alternating coefficient, rather
than merely producing an unspecified functional on a field sum. -/
theorem exists_on_fields
    (hk : protonFirstCharacter k = 1)
    {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (q' : Representation ℂ (GaugeGroup × H) Q)
    (u' : Representation ℂ (GaugeGroup × H) U)
    (e' : Representation ℂ (GaugeGroup × H) E)
    (eqQ : Equiv q' (q k)) (eqU : Equiv u' (u k)) (eqE : Equiv e' (e k)) :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient q' u' e', f ≠ 0 := by
  let eQ : Representation.Equiv (QqueSpinorExterior.qSpin q') (QqueSpinorExterior.qSpin (q k)) :=
    ExternalInvariantTensor.externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left)
  let eU : Representation.Equiv (QqueSpinorExterior.uSpin u') (QqueSpinorExterior.uSpin (u k)) :=
    ExternalInvariantTensor.externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right)
  let eE : Representation.Equiv (QqueSpinorExterior.eSpin e') (QqueSpinorExterior.eSpin (e k)) :=
    ExternalInvariantTensor.externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)
  let es := Math.SplitRepresentationProjection.prodEquiv eQ
    (Math.SplitRepresentationProjection.prodEquiv eU eE)
  let et := es.exteriorPower 4
  refine ⟨(coefficient k hk).comp et.toIntertwiningMap, ?_⟩
  intro hz
  apply coefficient_nonzero k hk
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := et.toLinearEquiv.surjective v
  exact LinearMap.congr_fun (congrArg IntertwiningMap.toLinearMap hz) z

end
end Physics.NeutralQqueExterior
