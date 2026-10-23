import Math.RepresentationTheory.Invariants.AutomorphismCovariantHom
import GUT.SU6.Characters.ContinuousUnitaryWeightDecomposition
import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex

open Physics

/-! Necessary data for ordinary SU(6) protection without strict UV commutation.
No protecting inhabitant or quantum-stability certificate is asserted. -/
open Math
namespace GUT.AutomorphismCovariantModel
set_option autoImplicit false
noncomputable section
open Representation ContinuousUnitaryWeightDecomposition
open Math.AutomorphismCovariantHom
open Physics.InvariantWeylMass

abbrev SU6 := CompactEmbeddingClassification.SU6

variable (H K : Type*) [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- Broken-phase model data, with a supplied automorphism action and fixed vacuum.
The target SM spectrum is deliberately a separate, typed application certificate. -/
structure Model where
  fermions : ContinuousUnitarySU6Representation
  scalars : ContinuousUnitarySU6Representation
  alpha : H →* MulAut SU6
  alpha_continuous : ∀ h, Continuous (alpha h)
  fermionAction : Action fermions.rho alpha
  scalarAction : Action scalars.rho alpha
  fermion_unitary : CompactEmbeddingClassification.IsUnitaryRepresentation fermionAction.residual
  scalar_unitary : CompactEmbeddingClassification.IsUnitaryRepresentation scalarAction.residual
  fermion_continuous : ContinuousRepresentationScope.IsJointlyContinuous fermionAction.residual
  scalar_continuous : ContinuousRepresentationScope.IsJointlyContinuous scalarAction.residual
  gauge : K →* SU6
  gauge_injective : Function.Injective gauge
  gauge_continuous : Continuous gauge
  beta : H →* MulAut K
  normalizes : ∀ h g, alpha h (gauge g) = gauge (beta h g)
  vev : scalars.V
  vev_gauge : ∀ g, scalars.rho (gauge g) vev = vev
  vev_residual : ∀ h, scalarAction.residual h vev = vev
  mass : SymmetricMass (fermions.rho.comp gauge)
  mass_residual : ∀ h x y, mass.form (fermionAction.residual h x)
    (fermionAction.residual h y) = mass.form x y

variable {H K} (M : Model H K)

/-- Residual mass invariance preserves actual zero modes, without a commuting premise. -/
theorem radical_stable (h : H) {v : M.fermions.V}
    (hv : v ∈ M.mass.radical.toSubmodule) :
    M.fermionAction.residual h v ∈ M.mass.radical.toSubmodule := by
  rw [SymmetricMass.mem_radical] at hv ⊢
  intro y
  have hy : M.fermionAction.residual h (M.fermionAction.residual h⁻¹ y) = y := by
    simp
  rw [← hy, M.mass_residual]
  exact hv _

/-- The exact radical carries the physical residual action. -/
def lightResidualSubrepresentation : Subrepresentation M.fermionAction.residual where
  toSubmodule := M.mass.radical.toSubmodule
  apply_mem_toSubmodule h _ hv := radical_stable M h hv

/-- Normalization of the unbroken gauge action is inherited from UV covariance. -/
theorem gauge_covariance (h : H) (g : K) (v : M.fermions.V) :
    M.fermionAction.residual h (M.fermions.rho (M.gauge g) v) =
      M.fermions.rho (M.gauge (M.beta h g)) (M.fermionAction.residual h v) := by
  rw [M.fermionAction.covariance, M.normalizes]

/-- Covariance descends to the actual light carrier, not just its character. -/
def lightAction : Action M.mass.radical.toRepresentation M.beta where
  residual := (lightResidualSubrepresentation M).toRepresentation
  covariance h g v := by
    apply Subtype.ext
    exact gauge_covariance M h g v.val

/-- Local-invariant residual functionals on actual zero modes descend to the
constructed local quotient. This is a linear-carrier interface, not dimension six. -/
def lightEquiv := Math.AutomorphismCovariantHom.equiv
  M.mass.radical.toRepresentation M.beta (lightAction M) (trivial ℂ H ℂ)

/-- A dual-index certificate on the actual mass radical. Applications must supply
an independently identified positive-generation SM target, not an arbitrary label. -/
def HasDualTarget {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (target : Representation ℂ K W) : Prop :=
  ∀ g, M.mass.radical.toRepresentation.character g -
    M.mass.radical.toRepresentation.dual.character g =
    target.character g - target.dual.character g

/-- Gauge-resolved positive-generation certificate relative to an independently
identified one-generation target. Gauge singlets have zero dual gauge index.
This does not impose a residual-charge-resolved target. -/
def HasPositiveDualTarget {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (oneGeneration : Representation ℂ K W) (n : ℕ) : Prop :=
  0 < n ∧ ∀ g, M.mass.radical.toRepresentation.character g -
    M.mass.radical.toRepresentation.dual.character g =
    (n : ℂ) * (oneGeneration.character g - oneGeneration.dual.character g)

/-- Gauge/residual-resolved target using the ordered gauge-then-residual trace.
No direct-product commutation or target matching is silently assumed. -/
def HasResolvedDualTarget {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (target : Representation ℂ K W)
    (targetAction : Action target M.beta) : Prop :=
  ∀ g h,
    LinearMap.trace ℂ _ (M.mass.radical.toRepresentation g *
      (lightAction M).residual h) -
    LinearMap.trace ℂ _ (M.mass.radical.toRepresentation.dual g *
      (lightAction M).residual.dual h) =
    LinearMap.trace ℂ _ (target g * targetAction.residual h) -
    LinearMap.trace ℂ _ (target.dual g * targetAction.residual.dual h)

/-- Gauge-invariant operators use the general covariant Hom descent when the
caller supplies their actual coefficient-carrier action. This model does not
construct that tensor/exterior action automatically. -/
def coefficientEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (localAction : Representation ℂ K V)
    (action : Action localAction M.beta) :=
  Math.AutomorphismCovariantHom.equiv localAction M.beta action (trivial ℂ H ℂ)

end
end GUT.AutomorphismCovariantModel
