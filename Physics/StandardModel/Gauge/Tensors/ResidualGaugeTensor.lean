import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Physics.StandardModel.Operators.Selection.AbelianProtonCharacter

open Math

/-!
# Residual Abelian selection rules on the actual SM gauge tensors

Each physical field carries its declared character. The tensor-product
actions recover exactly the existing Abelian proton-operator neutrality proton characters, including for
finite residual groups. No mass-radical identification is assumed or proved.
-/

set_option autoImplicit false

namespace Physics.StandardSMResidualTensor

noncomputable section

open StandardSMGaugeTensor FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H]

def charged {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) (chi : H →* Circle) :
    Representation ℂ (GaugeGroup × H) V where
  toFun g := (chi g.2 : ℂ) • rho g.1
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

def qqueRepresentation (k : Charges (ChargeLabel H)) :
    Representation ℂ (GaugeGroup × H) QQueSpace :=
  ((charged quark k.quark.toMul).tprod (charged quark k.quark.toMul)).tprod
    ((charged upRight (-k.up).toMul).tprod (charged electronRight (-k.electron).toMul))

def duqlRepresentation (k : Charges (ChargeLabel H)) :
    Representation ℂ (GaugeGroup × H) DuqlSpace :=
  ((charged downRight (-k.down).toMul).tprod (charged upRight (-k.up).toMul)).tprod
    ((charged quark k.quark.toMul).tprod (charged lepton k.lepton.toMul))

theorem qqueRepresentation_eq (k : Charges (ChargeLabel H)) :
    qqueRepresentation k = charged StandardSMGaugeTensor.qqueRepresentation
      (protonFirstCharacter k) := by
  apply MonoidHom.ext
  intro g
  simp [qqueRepresentation, StandardSMGaugeTensor.qqueRepresentation, charged,
    Representation.tprod_apply, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul, mul_comm, mul_assoc]

theorem duqlRepresentation_eq (k : Charges (ChargeLabel H)) :
    duqlRepresentation k = charged StandardSMGaugeTensor.duqlRepresentation
      (protonSecondCharacter k) := by
  apply MonoidHom.ext
  intro g
  simp [duqlRepresentation, StandardSMGaugeTensor.duqlRepresentation, charged,
    Representation.tprod_apply, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul, mul_comm, mul_assoc]

theorem qque_covariant (k : Charges (ChargeLabel H)) (g : GaugeGroup × H) (x : QQueSpace) :
    qque (qqueRepresentation k g x) = (protonFirstCharacter k g.2 : ℂ) * qque x := by
  rw [qqueRepresentation_eq]
  change qque ((protonFirstCharacter k g.2 : ℂ) •
    StandardSMGaugeTensor.qqueRepresentation g.1 x) = _
  rw [map_smul, ← LinearMap.comp_apply, qque_invariant_linear]
  rfl

theorem duql_covariant (k : Charges (ChargeLabel H)) (g : GaugeGroup × H) (x : DuqlSpace) :
    duql (duqlRepresentation k g x) = (protonSecondCharacter k g.2 : ℂ) * duql x := by
  rw [duqlRepresentation_eq]
  change duql ((protonSecondCharacter k g.2 : ℂ) •
    StandardSMGaugeTensor.duqlRepresentation g.1 x) = _
  rw [map_smul, ← LinearMap.comp_apply, duql_invariant_linear]
  rfl

theorem qque_invariant_iff (k : Charges (ChargeLabel H)) :
    (∀ g x, qque (qqueRepresentation k g x) = qque x) ↔ protonFirstCharacter k = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    have he := h (1, a) qqueWitness
    simpa [qque_covariant] using he
  · intro h g x
    rw [qque_covariant, h]
    simp

theorem duql_invariant_iff (k : Charges (ChargeLabel H)) :
    (∀ g x, duql (duqlRepresentation k g x) = duql x) ↔ protonSecondCharacter k = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    have he := h (1, a) duqlWitness
    simpa [duql_covariant] using he
  · intro h g x
    rw [duql_covariant, h]
    simp

def qqueIntertwiner (k : Charges (ChargeLabel H)) (hk : protonFirstCharacter k = 1) :
    Representation.IntertwiningMap (qqueRepresentation k)
      (Representation.trivial ℂ (GaugeGroup × H) ℂ) where
  toLinearMap := qque
  isIntertwining' g := by
    apply LinearMap.ext
    exact (qque_invariant_iff k).mpr hk g

def duqlIntertwiner (k : Charges (ChargeLabel H)) (hk : protonSecondCharacter k = 1) :
    Representation.IntertwiningMap (duqlRepresentation k)
      (Representation.trivial ℂ (GaugeGroup × H) ℂ) where
  toLinearMap := duql
  isIntertwining' g := by
    apply LinearMap.ext
    exact (duql_invariant_iff k).mpr hk g


/-- A group-independent conditional tensor result. Deriving charge compatibility
from an actual UV action is a separate source bridge. -/
theorem invariant_tensors_of_su5OrbitCompatible
    (k : Charges (ChargeLabel H)) (hk : SU5OrbitCompatible k) :
    qque ≠ 0 ∧ duql ≠ 0 ∧
      (∀ g x, qque (qqueRepresentation k g x) = qque x) ∧
      (∀ g x, duql (duqlRepresentation k g x) = duql x) := by
  obtain ⟨hFirst, hSecond⟩ := protonCharacters_eq_one_of_su5OrbitCompatible k hk
  exact ⟨qque_nonzero, duql_nonzero,
    (qque_invariant_iff _).mpr hFirst, (duql_invariant_iff _).mpr hSecond⟩

end

end Physics.StandardSMResidualTensor
