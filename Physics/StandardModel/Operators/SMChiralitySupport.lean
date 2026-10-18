import Physics.StandardModel.Operators.SMMixedCompactWeyl
import Physics.StandardModel.Operators.SMParityKernelRank

/-! Independent chirality parity excludes actual mixed contents at every degree. -/
namespace GUT.SMChiralitySupport
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

def center (side : Bool) : WeylIndependentAction.Group :=
  if side then (1,WeylCentralParity.minusIdentity) else (WeylCentralParity.minusIdentity,1)

def slotCount (side : Bool) (s : DeltaLOneSignedInput.Species) : ℕ :=
  if DeltaLOneSignedFields.rightHanded s=side then 1 else 0

def count {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (side : Bool) : ℕ :=
  ∑ i, slotCount side (p i)

theorem spin_center (side b : Bool) (x : WeylSpinor.Space) :
    WeylIndependentAction.spin b (center side) x =
      (-1 : ℂ)^(if b=side then 1 else 0) • x := by
  cases side <;> cases b
  · simpa [WeylIndependentAction.spin, center, FourSameWeylCompleteness.action] using WeylCentralParity.action_minus false x
  · simp [WeylIndependentAction.spin, center]
  · simp [WeylIndependentAction.spin, center]
  · simpa [WeylIndependentAction.spin, center, FourSameWeylCompleteness.action] using WeylCentralParity.action_minus false x

theorem field_center (side : Bool) (s : DeltaLOneSignedInput.Species)
    (x : DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :
    SMMixedCompactWeyl.field s (center side) x = (-1 : ℂ)^(slotCount side s) • x := by
  have hs : WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s) (center side) =
      (-1 : ℂ)^(slotCount side s) • LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact spin_center side _ v
  change TensorProduct.map (TensorProduct.map LinearMap.id
    (WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s) (center side)))
    LinearMap.id x = _
  rw [hs, TensorProduct.map_smul_right, TensorProduct.map_id,
    TensorProduct.map_smul_left, TensorProduct.map_id]
  rfl

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

omit flavor in
theorem raw_center (side : Bool) : PatternExteriorSource.Raw SMMixedCompactWeyl.field p
    (center side) = (-1 : ℂ)^(count p side) • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearInvariantHom.tensorRepresentation_tprod]
  simp_rw [field_center]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ, Finset.prod_pow_eq_pow_sum]
  rfl

theorem source_center (side : Bool)
    (x : PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :
    SMMixedCompactWeyl.source flavor p (center side) x = (-1 : ℂ)^(count p side) • x :=
  PatternExteriorSource.source_scalar SMMixedCompactWeyl.field p (center side) _ (raw_center p side) x

theorem action_center (side : Bool) (m : ℕ) :
    SMMixedCompactWeyl.action flavor p m (center side) = (-1 : ℂ)^(count p side) • LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change SMMixedCompactWeyl.source flavor p (center side) x ⊗ₜ[ℂ] y =
    (-1 : ℂ)^(count p side) • (x ⊗ₜ[ℂ] y)
  simpa only [TensorProduct.smul_tmul'] using
    congrArg (fun z => z ⊗ₜ[ℂ] y) (source_center flavor p side x)

theorem independent_fixed (m : ℕ) (delta : ℤ)
    (f : InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta)) :
    ∀ g x, f (SMMixedCompactWeyl.action flavor p m g x)=f x := by
  have hs := PairedPolynomialInvariants.fixed_iff_action (SMMixedCompactWeyl.action flavor p m)
    WeylSpinor.conjugate WeylIndependentAction.family WeylIndependentAction.family_generates
    WeylIndependentAction.family_conjugate WeylIndependentAction.family_zero
    (SMMixedCompactWeyl.action_polynomial flavor p m)
    (SMWeylFiniteKernel.action flavor p m delta) (SMMixedCompactWeyl.action_paired flavor p m delta)
    f.toLinearMap
  apply hs.mp
  intro g x
  exact f.isIntertwining _ _ (1,g) x

theorem local_forbidden (side : Bool) (ho : count p side % 2 ≠ 0) (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) := by
  intro f
  let t : InvariantCoefficientTransport.Invariants (SMMixedCompactWeyl.action flavor p m) := {
    toLinearMap := f.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact independent_fixed flavor p m delta f g x }
  have hp : Odd (count p side) := Nat.odd_iff.mpr (by omega)
  have hz := MixedScalarSelection.invariant_zero (SMMixedCompactWeyl.action flavor p m)
    (center side) ((-1 : ℂ)^(count p side)) (by rw [hp.neg_one_pow]; norm_num)
    (fun x => LinearMap.congr_fun (action_center flavor p side m) x) t
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hz x

def restrictLocal (m : ℕ) (delta : ℤ) (f : SMFiniteHiggsSupport.Test flavor p m delta) :
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (g,1)

theorem test_forbidden (side : Bool) (ho : count p side % 2 ≠ 0) (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.Test flavor p m delta) := by
  intro f
  have hz := local_forbidden flavor p side ho m delta (restrictLocal flavor p m delta f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hz x

theorem original_forbidden (side : Bool) (ho : count p side % 2 ≠ 0) (h d : ℕ) :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace flavor p h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, SMFiniteHiggsSupport.original_allowed_iff]
  rintro ⟨m,_,ha⟩
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (test_forbidden flavor p side ho m.val ((h : ℤ)-d)) ha

end
end GUT.SMChiralitySupport
