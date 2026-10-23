import Math.RepresentationTheory.Jets.NonDerivativeInputChecks
import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP
import Physics.FieldTheory.Spinor.Weyl.WeylCentralParity

/-! Actual Lorentz mass/Yukawa and odd-Weyl controls through both inputs. -/
namespace Physics.WeylNonDerivativeChecks
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

@[reducible] local instance (n m : ℕ) :
    AddCommGroup (MixedJetSource.Original (Fin 2) Unit n m) := inferInstance
@[reducible] local instance (n m : ℕ) :
    Module ℂ (MixedJetSource.Original (Fin 2) Unit n m) := inferInstance

abbrev fermions := LorentzJetIBP.weyl false
abbrev bosons := LorentzJetIBP.scalarField
abbrev directions := LorentzDirections.direction

def value (m : ℕ) : MixedJetSource.Original (Fin 2) Unit 2 m →ₗ[ℂ] ℂ :=
  (NonDerivativeInputChecks.Statistics.oldMixed m).toLinearMap

theorem value_pure (m : ℕ) (v : Fin 2 → JetLinear.Field (Fin 2))
    (w : Fin m → JetLinear.Field Unit) :
    value m (MixedWeightSupport.pure v w) =
      SMEpsilonTensor.eps2 (LorentzJetIBP.spinorBasis (v 0))
        (LorentzJetIBP.spinorBasis (v 1)) * ∏ i, w i () := by
  simp [value,NonDerivativeInputChecks.Statistics.oldMixed,
    NonDerivativeInputChecks.Statistics.unitInvariant,MixedWeightSupport.pure,
    NonDerivativeInputChecks.Statistics.oddValue,
    NonDerivativeInputChecks.Statistics.evenValue,
    NonDerivativeInputChecks.Statistics.bosonProduct,SymmetricPowerDescent.lift_tprod,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Module.Basis.det_apply,Module.Basis.toMatrix_apply,Matrix.det_fin_two,
    SMEpsilonTensor.eps2,LorentzJetIBP.spinorBasis,mul_comm]

theorem epsilon_invariant (g : LorentzJetIBP.Group) (x y : WeylSpinor.Space) :
    SMEpsilonTensor.eps2 (WeylSpinor.left g x) (WeylSpinor.left g y) =
      SMEpsilonTensor.eps2 x y := by
  exact IntertwiningMap.isIntertwining _ _ WeylSpinor.epsilonLeft g (x ⊗ₜ[ℂ] y)

def old (m : ℕ) : NonDerivativeInputChecks.Bridge.Old fermions bosons 2 m where
  toLinearMap := value m
  isIntertwining' g := by
    apply MixedPowerDescent.ext 2 m
    intro v w
    change value m ((fermions.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ]
      (bosons.symmetricPower m) g (SymmetricPower.tprod ℂ w)) =
      value m (MixedWeightSupport.pure v w)
    rw [Representation.exteriorPower_apply_ιMulti,Representation.symmetricPower_apply_tprod]
    change value m (MixedWeightSupport.pure (fermions g ∘ v) (bosons g ∘ w)) = _
    rw [value_pure,value_pure]
    simp only [Function.comp_apply,LorentzJetIBP.weyl_basis,Bool.false_eq_true,ite_false]
    rw [epsilon_invariant]
    rfl

def unified (m : ℕ) := NonDerivativeInputChecks.Bridge.toUnified
  fermions bosons directions 2 m (old m)

theorem normalized (m : ℕ) :
    (unified m).val (MixedJetSource.zeroEquiv 2 m
      (NonDerivativeInputChecks.Statistics.mixedWord m Finsupp.basisSingleOne)) = 1 := by
  trans old m (NonDerivativeInputChecks.Statistics.mixedWord m Finsupp.basisSingleOne)
  · exact NonDerivativeInputChecks.Bridge.extraction fermions bosons directions 2 m (old m) _
  · exact (NonDerivativeInputChecks.Statistics.old_mixed_value m _).trans
      (Module.Basis.det_self _)

theorem nonzero (m : ℕ) : unified m ≠ 0 := by
  intro hz
  have h := normalized m
  rw [hz] at h
  exact zero_ne_one h

theorem swap_value (m : ℕ) :
    (unified m).val (MixedJetSource.zeroEquiv 2 m
      (NonDerivativeInputChecks.Statistics.mixedWord m
        ![Finsupp.single 1 1,Finsupp.single 0 1])) = -1 := by
  trans old m (NonDerivativeInputChecks.Statistics.mixedWord m
    ![Finsupp.single 1 1,Finsupp.single 0 1])
  · exact NonDerivativeInputChecks.Bridge.extraction fermions bosons directions 2 m (old m) _
  · change NonDerivativeInputChecks.Statistics.oldMixed m
      (NonDerivativeInputChecks.Statistics.mixedWord m _) = -1
    rw [NonDerivativeInputChecks.Statistics.old_mixed_value]
    simp [Module.Basis.det_apply,Module.Basis.toMatrix_apply,Matrix.det_fin_two]

theorem inverse (m : ℕ) :
    (NonDerivativeInputChecks.Bridge.toUnified fermions bosons directions 2 m).symm
      (unified m) = old m := LinearEquiv.symm_apply_apply _ _

theorem field_minus (v : JetLinear.Field (Fin 2)) :
    fermions WeylCentralParity.minusIdentity v = (-1 : ℂ) • v := by
  apply LorentzJetIBP.spinorBasis.injective
  rw [LorentzJetIBP.weyl_basis,map_smul]
  exact WeylCentralParity.action_minus false _

theorem odd_forbidden (m : ℕ)
    (f : NonDerivativeInputChecks.Bridge.Old fermions bosons 1 m) : f = 0 := by
  apply IntertwiningMap.ext
  apply MixedPowerDescent.ext 1 m
  intro v w
  have hv : exteriorPower.ιMulti ℂ 1 (fun i => (-1 : ℂ) • v i) =
      (-1 : ℂ) • exteriorPower.ιMulti ℂ 1 v := by
    simpa only [Fin.prod_univ_one] using
      (exteriorPower.ιMulti ℂ 1).map_smul_univ (fun _ => (-1 : ℂ)) v
  have hp : MixedJetSource.originalAction fermions bosons 1 m
      WeylCentralParity.minusIdentity (MixedWeightSupport.pure v w) =
        (-1 : ℂ) • MixedWeightSupport.pure v w := by
    change ((fermions.exteriorPower 1) _ (exteriorPower.ιMulti ℂ 1 v)) ⊗ₜ[ℂ]
      ((bosons.symmetricPower m) _ (SymmetricPower.tprod ℂ w)) = _
    rw [Representation.exteriorPower_apply_ιMulti,Representation.symmetricPower_apply_tprod]
    have he : fermions WeylCentralParity.minusIdentity ∘ v =
        fun i => (-1 : ℂ) • v i := funext fun i => field_minus (v i)
    rw [he,hv,← TensorProduct.smul_tmul']
    rfl
  have h := IntertwiningMap.isIntertwining _ _ f WeylCentralParity.minusIdentity
    (MixedWeightSupport.pure v w)
  change f.toLinearMap (MixedJetSource.originalAction fermions bosons 1 m
    WeylCentralParity.minusIdentity (MixedWeightSupport.pure v w)) =
    f.toLinearMap (MixedWeightSupport.pure v w) at h
  rw [hp,map_smul] at h
  change f.toLinearMap (MixedWeightSupport.pure v w) = 0
  change (-1 : ℂ) * f.toLinearMap (MixedWeightSupport.pure v w) =
    f.toLinearMap (MixedWeightSupport.pure v w) at h
  linear_combination (-1/2 : ℂ) * h

theorem unified_odd_forbidden (m : ℕ) :
    ∀ f : (DerivativeInterface.graded fermions bosons directions 1 m 0).Coefficient, f = 0 :=
  (NonDerivativeInputChecks.Bridge.forbidden_iff fermions bosons directions 1 m).mp
    (odd_forbidden m)

end
end Physics.WeylNonDerivativeChecks
