import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCauchy
import Math.RepresentationTheory.Invariants.FactoredInvariantSupport

/-! Charge-neutral extension from the semisimple subgroup, at symbolic content. -/
namespace Physics.SMCombinedChargeSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy
open scoped TensorProduct

def hyper : Circle →* SMCombinedCompactAction.Group where
  toFun z := (DeltaLOneSignedFields.hyperchargeElement z, 1)
  map_one' := rfl
  map_mul' _ _ := by simp [DeltaLOneSignedFields.hyperchargeElement]

theorem decomposition (g : SMCombinedCompactAction.Group) :
    g = inclusion (g.1.1, (g.1.2.1, g.2)) * hyper g.1.2.2 := by
  simp [inclusion, hyper, DeltaLOneSignedFields.hyperchargeElement]

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem source_hyper (z : Circle) (x : PatternExteriorSource.Source
    (DeltaLOneSignedFields.field flavor) p) :
    SMCombinedCompactAction.source flavor p (hyper z) x =
      (z : ℂ)^(SMContentWeakBound.hypercharge p) • x := by
  have he := congrArg (fun r => r (DeltaLOneSignedFields.hyperchargeElement z) x)
    (SMCombinedCompactAction.source_gauge flavor p)
  change SMCombinedCompactAction.source flavor p (hyper z) x =
    SMContentWeakBound.source flavor p (DeltaLOneSignedFields.fullHypercharge z) x at he
  exact he.trans (SMContentWeakBound.source_hypercharge flavor p z x)

theorem action_hyper (m : ℕ) (delta : ℤ) (z : Circle)
    (x : SMFullLocalKernel.Carrier flavor p m) :
    SMCombinedCompactAction.action flavor p m delta (hyper z) x =
      (z : ℂ)^(SMContentWeakBound.hypercharge p + 3*delta) • x := by
  have hb (y : Sym[ℂ]^m WeakDoubletScalars.Doublet) :
      SMCombinedCompactAction.boson (H := H) m delta (hyper z) y =
        (z : ℂ)^(3*delta) • y :=
    SMFiniteHiggsSupport.constituent_hypercharge m delta z y
  have he : SMCombinedCompactAction.action flavor p m delta (hyper z) =
      (z : ℂ)^(SMContentWeakBound.hypercharge p + 3*delta) • LinearMap.id := by
    apply TensorProduct.ext'
    intro a b
    change SMCombinedCompactAction.source flavor p (hyper z) a ⊗ₜ[ℂ]
      SMCombinedCompactAction.boson (H := H) m delta (hyper z) b =
        (z : ℂ)^(SMContentWeakBound.hypercharge p + 3*delta) • (a ⊗ₜ[ℂ] b)
    rw [source_hyper flavor p z a, hb b, TensorProduct.smul_tmul_smul]
    congr 1
    exact (zpow_add₀ z.coe_ne_zero _ _).symm
  exact LinearMap.congr_fun he x

theorem hyper_neutral (m : ℕ) (delta : ℤ)
    (hc : SMContentWeakBound.hypercharge p + 3*delta = 0) (z : Circle)
    (x : SMFullLocalKernel.Carrier flavor p m) :
    SMCombinedCompactAction.action flavor p m delta (hyper z) x = x := by
  rw [action_hyper, hc, zpow_zero, one_smul]

theorem allowed (m : ℕ) (delta : ℤ) (hc : SMContentWeakBound.hypercharge p + 3*delta = 0)
    (h : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor p m delta).comp inclusion))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMCombinedCompactAction.action flavor p m delta)) :=
  FactoredInvariantSupport.allowed (SMCombinedCompactAction.action flavor p m delta)
    inclusion hyper (fun g => ⟨_,_,decomposition g⟩)
    (hyper_neutral flavor p m delta hc) h

end
end Physics.SMCombinedChargeSupport
