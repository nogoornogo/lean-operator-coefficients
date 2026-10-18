import GUT.SU5.SelectionRules.ActualFullFamilyQque
import Physics.StandardModel.Operators.ResidualQquePrefilter

/-! Joint SM-copy and residual-action constraints, with an explicit radical bridge. -/
namespace GUT.SU5.FullFamilyResidualPrefilter
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor ActualFullFamilyIndex
open InvariantWeylMass
local instance : AddCommGroup Matter.Ten := inferInstance
local instance : AddCommGroup FortyHyperchargeExclusion.Kernel := inferInstance
local instance : Module ℂ FortyHyperchargeExclusion.Kernel := inferInstance
local instance : AddCommGroup ExoticHyperchargeBasis.Fifty := inferInstance
local instance : Module ℂ ExoticHyperchargeBasis.Fifty := inferInstance
variable {H F : Type} [CommGroup H] [AddCommGroup F] [Module ℂ F]
    (p q : Counts) (B : SymmetricMass (fields p q))
    (tau : Representation ℂ (GaugeGroup × H) F)

/-- The residual action really acts on the original mass radical. Its gauge
restriction is identified, rather than reconstructed from numerical counts. -/
theorem protected_constraints (N : ℕ)
    (bridge : Equiv (ProductFactorization.firstRestriction tau) B.radical.toRepresentation)
    (sm : Equiv (ProductFactorization.firstRestriction tau) (FiniteSpectrum.copies N smGeneration))
    (hp : ResidualQquePrefilter.Forbids tau) :
    ((p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3) ∧
      ResidualQquePrefilter.Necessary tau := by
  exact ⟨net_constraints_of_exact_sm p q B N (bridge.symm.trans sm),
    ResidualQquePrefilter.necessary tau hp⟩

/-- Either failed necessary test rejects simultaneous exact-SM content and
prohibition. This exposes a single combined input-side exclusion predicate. -/
theorem joint_reject (N : ℕ)
    (bridge : Equiv (ProductFactorization.firstRestriction tau) B.radical.toRepresentation)
    (hbad : ¬ ((p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3) ∨
      ¬ ResidualQquePrefilter.Necessary tau) :
    ¬ (Nonempty (Equiv (ProductFactorization.firstRestriction tau)
      (FiniteSpectrum.copies N smGeneration)) ∧ ResidualQquePrefilter.Forbids tau) := by
  rintro ⟨⟨sm⟩, hp⟩
  have hc := protected_constraints p q B tau N bridge sm hp
  rcases hbad with h | h
  · exact h hc.1
  · exact h hc.2

/-- Neutrality excludes protection even when the SM copy prefilter passes.
The explicit subspace dictionary is what makes this a physical exclusion. -/
theorem neutral_reject (X : ResidualQquePrefilter.Triplet tau)
    (h : FiniteAbelianChargeSectors.protonFirstCharacter X.charges = 1) :
    ¬ ResidualQquePrefilter.Forbids tau :=
  ResidualQquePrefilter.neutral_excludes tau X h
section UniformSM
variable (chi : H →* Circle)
abbrev uniformSM := StandardSMResidualTensor.charged smGeneration chi

def uniformTriplet : ResidualQquePrefilter.Triplet (uniformSM chi) := by
  let fq := ResidualQquePrefilter.chargedMap ActualFullFamilyQque.qGeneration chi
  let fu := ResidualQquePrefilter.chargedMap ActualFullFamilyQque.uGeneration chi
  let fe := ResidualQquePrefilter.chargedMap ActualFullFamilyQque.eGeneration chi
  have hq : Function.Injective fq := ActualFullFamilyQque.qGeneration_injective
  have hu : Function.Injective fu := ActualFullFamilyQque.uGeneration_injective
  have he : Function.Injective fe := ActualFullFamilyQque.eGeneration_injective
  let k : StandardBranchProtonObstruction.Charges
      (Math.FiniteAbelianChargeSectors.ChargeLabel H) :=
    ⟨Additive.ofMul chi, Additive.ofMul chi, Additive.ofMul chi,
      Additive.ofMul chi, Additive.ofMul chi⟩
  exact ⟨k, fq.range, fu.range, fe.range,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fq hq).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fu hu).symm,
    (UnitarySubrepresentationOrthogonality.rangeEquiv fe he).symm⟩

/-- This control has the actual complete one-generation SM gauge content,
including down and lepton species, independently of the residual character. -/
theorem uniformSM_gauge : ProductFactorization.firstRestriction (uniformSM chi) = smGeneration := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (chi 1 : ℂ) • smGeneration g v = smGeneration g v
  simp

theorem uniformSM_reject : ¬ ResidualQquePrefilter.Forbids (uniformSM chi) :=
  ResidualQquePrefilter.equal_species_excludes _ (uniformTriplet chi) rfl rfl
end UniformSM
end
end GUT.SU5.FullFamilyResidualPrefilter
