import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactWeyl
import Math.RepresentationTheory.Coefficients.SeparatedInvariantCoefficients

/-! Gauge/residual-retaining compact Weyl coefficient constraints and actual kernels. -/
namespace Physics.SMMixedCompactCoefficients
set_option autoImplicit false
noncomputable section
open Math Representation
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)

abbrev compactSpin := (SMMixedCompactWeyl.action flavor p m).comp SMMixedCompactWeyl.compact

def retained : (StandardSMGaugeTensor.GaugeGroup × H) →* NeutralHiggsPowers.G H where
  toFun b := ((b.1,1),b.2)
  map_one' := rfl
  map_mul' _ _ := by simp

theorem full_decomposition (g : NeutralHiggsPowers.G H) :
    ∃ b w, g = retained b * SMWeylFiniteKernel.inclusion w := by
  refine ⟨(g.1.1,g.2),g.1.2,?_⟩
  simp [retained,SMWeylFiniteKernel.inclusion]

/-- Gauge and arbitrary residual conditions are retained verbatim. -/
abbrev FullSpace := SeparatedInvariantCoefficients.Space
  (SMWeylFiniteKernel.fullAction flavor p m delta) (retained (H := H)) (compactSpin flavor p m)

def fullEquiv : InvariantCoefficientTransport.Invariants (SMWeylFiniteKernel.fullAction flavor p m delta)
    ≃ₗ[ℂ] FullSpace flavor p m delta :=
  SeparatedInvariantCoefficients.equiv (V := SMFullLocalKernel.Carrier flavor p m)
    (SMWeylFiniteKernel.fullAction flavor p m delta) (retained (H := H))
    (SMWeylFiniteKernel.inclusion (H := H)) (compactSpin flavor p m)
    (full_decomposition (H := H))
    (fun f => SMMixedCompactWeyl.coefficient_fixed_iff flavor p m delta f)

abbrev LocalSpace := SeparatedInvariantCoefficients.Space
  (SMIntegralLocalWeights.action flavor p m delta)
    (MonoidHom.inl StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group) (compactSpin flavor p m)

theorem local_decomposition (g : SMIntegralLocalWeights.Group) :
    ∃ b w, g = MonoidHom.inl StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group b *
      SMIntegralLocalWeights.spin w := by
  exact ⟨g.1,g.2,by simp [SMIntegralLocalWeights.spin]⟩

def localEquiv : InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta)
    ≃ₗ[ℂ] LocalSpace flavor p m delta :=
  SeparatedInvariantCoefficients.equiv _ _ SMIntegralLocalWeights.spin _ local_decomposition
    (fun f => SMMixedCompactWeyl.coefficient_fixed_iff flavor p m delta f)

/-- The entire compact constraint space maps to the previously certified actual kernel. -/
def kernelEquiv : LocalSpace flavor p m delta ≃ₗ[ℂ] SMFullLocalKernel.Kernel flavor p m delta :=
  (localEquiv flavor p m delta).symm.trans (SMFullLocalKernel.coefficientEquiv flavor p m delta)

theorem kernel_dimension : Module.finrank ℂ (LocalSpace flavor p m delta) =
    Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) :=
  (kernelEquiv flavor p m delta).finrank_eq

theorem allowed_iff : SelectionCriteria.Allowed (LocalSpace flavor p m delta) ↔
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor p m delta) :=
  SelectionCriteria.allowed_equiv (kernelEquiv flavor p m delta)

/-- Original arbitrary Higgs degrees retain full gauge/residual conditions, with compact Weyl tests. -/
theorem original_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace flavor p h d) ↔
      ∃ j : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d j.val ∧
        SelectionCriteria.Allowed (FullSpace flavor p j.val ((h : ℤ)-d)) := by
  refine (SMFiniteHiggsSupport.original_allowed_iff flavor p h d).trans ?_
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  exact SelectionCriteria.allowed_equiv (fullEquiv flavor p j.val ((h : ℤ)-d))

end
end Physics.SMMixedCompactCoefficients
