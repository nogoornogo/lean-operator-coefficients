import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientCompleteness

open Math

/-! A literal, normalized local contraction interpretation of Li et al. (D.38).
The paper order is Q,Q,E,U. This is not a general on-shell amplitude theorem.
The left/right spinor bases normalize both brackets to `eps2`; physical LSZ
normalizations and package runtime output are not inputs to these results. -/
namespace Physics.LiQqueConvention
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
  QqueSpinorExterior QqueCoefficientAssembly SMEpsilonTensor
open scoped TensorProduct

variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] Module.Dual ℂ B) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D) := inferInstance

/-- Algebraic gauge/flavor dictionary before taking the dagger. Spin is left Weyl. -/
abbrev uc := external StandardSMGaugeTensor.upRight.dual b
abbrev ec := external StandardSMGaugeTensor.electronRight.dual d
/-- Dagger dualizes gauge and flavor; its Weyl action is right. -/
abbrev ucDagger := external StandardSMGaugeTensor.upRight.dual.dual b.dual
abbrev ecDagger := external StandardSMGaugeTensor.electronRight.dual.dual d.dual

def ucDaggerEquiv : Representation.Equiv (ucDagger b) (uField (b := b)) :=
  externalEquiv (bidualEquiv StandardSMGaugeTensor.upRight).symm
    (Representation.Equiv.refl b.dual)

def ecDaggerEquiv : Representation.Equiv (ecDagger d) (eField (d := d)) :=
  externalEquiv (bidualEquiv StandardSMGaugeTensor.electronRight).symm
    (Representation.Equiv.refl d.dual)

/-- Reindex only the two singlet slots, before imposing Fermi statistics. -/
def singletSwap : Representation.Equiv
    (((qSpin (qField (a := a))).tprod (qSpin (qField (a := a)))).tprod
      ((eSpin (eField (d := d))).tprod (uSpin (uField (b := b)))))
    (((qSpin (qField (a := a))).tprod (qSpin (qField (a := a)))).tprod
      ((uSpin (uField (b := b))).tprod (eSpin (eField (d := d))))) where
  toLinearEquiv := TensorProduct.congr (LinearEquiv.refl ℂ _)
    (TensorProduct.comm ℂ _ _)
  isIntertwining' g := by ext x y e u; rfl

/-- In Q,Q,E,U order, [34] pairs the electron spinor first. Thus the
normalized printed contraction is minus the ungraded singlet pullback. -/
def paperOrdered (f : ResidualCoefficient a b d) :=
  -((ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f)).comp
    (singletSwap a b d).toIntertwiningMap)

theorem paperOrdered_apply (f : ResidualCoefficient a b d)
    (c₁ c₂ c₄ : Color) (w₁ w₂ : Weak) (m : ℂ)
    (x y : A) (u : Module.Dual ℂ B) (e : Module.Dual ℂ D)
    (s₁ s₂ s₃ s₄ : WeylSpinor.Space) :
    paperOrdered a b d f
      (((((c₁ ⊗ₜ[ℂ] w₁) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s₁) ⊗ₜ[ℂ]
        (((c₂ ⊗ₜ[ℂ] w₂) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] s₂)) ⊗ₜ[ℂ]
        (((m ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] s₃) ⊗ₜ[ℂ] ((c₄ ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] s₄))) =
      eps3 c₁ c₂ c₄ * eps2 w₁ w₂ * m *
        f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) * (eps2 s₁ s₂ * eps2 s₃ s₄) := by
  change -(ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f)
    (((((c₁ ⊗ₜ[ℂ] w₁) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s₁) ⊗ₜ[ℂ]
      (((c₂ ⊗ₜ[ℂ] w₂) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] s₂)) ⊗ₜ[ℂ]
      (((c₄ ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] s₄) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] s₃)))) = _
  rw [ordered_apply, ExplicitSMResidualTensor.qque_tmul, StandardSMGaugeTensor.qque_tmul]
  simp only [eps2]
  ring

/-- The additional minus is the parity of the fermionic singlet transposition.
The bracket reversal and Fermi sign cancel, as an equality of full linear maps. -/
theorem fermionic_reorder (f : ResidualCoefficient a b d) :
    -(paperOrdered a b d f).comp (singletSwap a b d).symm.toIntertwiningMap =
      ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual f) := by
  apply IntertwiningMap.ext
  ext x y u e
  change -(-(_)) = _
  exact neg_neg _

/-- The actual candidate lands in the independently specified exterior sector. -/
def candidate (f : symmetricCoefficients a b d) : QqueCoefficientCompleteness.Sector a b d :=
  ⟨FourSlotAlternation.coefficient _ _ _
      (-(paperOrdered a b d f.val).comp (singletSwap a b d).symm.toIntertwiningMap),
    QqueCoefficientSector.alternation_mem _ _ _ _⟩

theorem candidate_eq (f : symmetricCoefficients a b d) :
    (candidate a b d f).val = assemble a b d f.val := by
  change FourSlotAlternation.coefficient _ _ _
    (-(paperOrdered a b d f.val).comp (singletSwap a b d).symm.toIntertwiningMap) = _
  rw [fermionic_reorder]
  rfl

/-- Raw four-slot alternatization has factor two on the symmetric probe. -/
theorem candidate_probe (f : symmetricCoefficients a b d) (x y : A)
    (u : Module.Dual ℂ B) (e : Module.Dual ℂ D) :
    (candidate a b d f).val (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 0)
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] weakBasis 1)
      ((colorBasis 2 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] weakBasis 0)
      (((1 : ℂ) ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] weakBasis 1))) =
      2 * f.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  rw [candidate_eq, probe, f.property x y u e]
  ring

variable [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]

/-- Completeness of the literal normalized D.38 candidate family. -/
def equiv : symmetricCoefficients a b d ≃ₗ[ℂ] QqueCoefficientCompleteness.Sector a b d :=
  (QqueResidualHom.equiv a b d).trans (QqueCoefficientCompleteness.equiv a b d)

set_option maxHeartbeats 400000 in
theorem equiv_apply (f : symmetricCoefficients a b d) :
    equiv a b d f = candidate a b d f := by
  apply Subtype.ext
  rw [candidate_eq]
  change assemble a b d (((QqueResidualHom.equiv a b d).symm
    (QqueResidualHom.equiv a b d f)).val) = _
  rw [LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 400000 in
theorem candidate_fromHom_eq (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d)) :
    candidate a b d ((QqueResidualHom.equiv a b d).symm f) =
      QqueCoefficientCompleteness.equiv a b d f := by
  calc
    candidate a b d ((QqueResidualHom.equiv a b d).symm f) =
        equiv a b d ((QqueResidualHom.equiv a b d).symm f) :=
      (equiv_apply a b d _).symm
    _ = QqueCoefficientCompleteness.equiv a b d
        (QqueResidualHom.equiv a b d ((QqueResidualHom.equiv a b d).symm f)) := rfl
    _ = QqueCoefficientCompleteness.equiv a b d f :=
      congrArg (QqueCoefficientCompleteness.equiv a b d)
        ((QqueResidualHom.equiv a b d).apply_symm_apply f)

/-- The daggered gauge dictionary has a constructed, rather than assumed, bridge. -/
def onDaggerFieldsEquiv : IntertwiningMap (a.symmetricPower 2) (b.tprod d) ≃ₗ[ℂ]
    QqueCoefficientSector.sector (qField (a := a)) (ucDagger b) (ecDagger d) :=
  QqueCoefficientCompleteness.onFieldsEquiv a b d _ _ _
    (Representation.Equiv.refl _) (ucDaggerEquiv b) (ecDaggerEquiv d)


/-- Pullback of actual candidate coefficients through the constructed dagger dictionary. -/
def daggerTransport : QqueCoefficientCompleteness.Sector a b d ≃ₗ[ℂ]
    QqueCoefficientSector.sector (qField (a := a)) (ucDagger b) (ecDagger d) :=
  FourSlotSpeciesTransport.equiv
    (externalEquiv (Representation.Equiv.refl (qField (a := a)))
      (Representation.Equiv.refl WeylSpinor.left))
    (externalEquiv (ucDaggerEquiv b) (Representation.Equiv.refl WeylSpinor.right))
    (externalEquiv (ecDaggerEquiv d) (Representation.Equiv.refl WeylSpinor.right))

set_option maxHeartbeats 400000 in
theorem onDaggerFields_candidate (f : symmetricCoefficients a b d) :
    onDaggerFieldsEquiv a b d (QqueResidualHom.equiv a b d f) =
      daggerTransport a b d (candidate a b d f) :=
  congrArg (daggerTransport a b d) (equiv_apply a b d f)

end
end Physics.LiQqueConvention
