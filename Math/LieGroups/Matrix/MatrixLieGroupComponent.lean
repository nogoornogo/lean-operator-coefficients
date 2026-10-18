import Math.LieGroups.Matrix.MatrixLieGroupNormalizer
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Identity component of the closed matrix normalizer

Continuous exponential lines lie in the identity component. This uses
connectedness only, not a closed-subgroup manifold or integration theorem.
-/

set_option autoImplicit false

namespace Math.MatrixLieGroupNormalizer

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (L : LieSubalgebra ℝ (Matrix n n ℂ))

abbrev identityComponent : Subgroup (subgroup L) :=
  Subgroup.connectedComponentOfOne (subgroup L)

theorem isClosed_identityComponent : IsClosed (identityComponent L : Set (subgroup L)) :=
  isClosed_connectedComponent

theorem isConnected_identityComponent : IsConnected (identityComponent L : Set (subgroup L)) :=
  isConnected_connectedComponent

instance : CompactSpace (identityComponent L) :=
  isCompact_iff_compactSpace.mp (isClosed_identityComponent L).isCompact

instance : ConnectedSpace (identityComponent L) :=
  Subtype.connectedSpace (isConnected_identityComponent L)

def componentMatrices : Submonoid (Matrix n n ℂ) :=
  (identityComponent L).toSubmonoid.map
    ((Matrix.specialUnitaryGroup n ℂ).subtype.comp (subgroup L).subtype)

theorem mem_componentMatrices (A : Matrix n n ℂ) : A ∈ componentMatrices L ↔
    ∃ g : subgroup L, g ∈ identityComponent L ∧ (g.val : Matrix n n ℂ) = A := Iff.rfl

theorem componentMatrices_le : componentMatrices L ≤ matrixCarrier L := by
  rintro A ⟨g, _, rfl⟩
  exact ⟨g.val, g.property, rfl⟩

/-- Bundle an already proved all-time exponential line in the actual subgroup. -/
def exponentialLine (X : Matrix n n ℂ) (hX : ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L)
    (t : ℝ) : subgroup L :=
  ⟨⟨exp (t • X), matrixCarrier_le_special L (hX t)⟩, by
    obtain ⟨g, hg, he⟩ := (mem_matrixCarrier L _).mp (hX t)
    have heq : g = ⟨exp (t • X), matrixCarrier_le_special L (hX t)⟩ := Subtype.ext he
    exact heq ▸ hg⟩

@[simp] theorem exponentialLine_coe (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L) (t : ℝ) :
    ((exponentialLine L X hX t).val : Matrix n n ℂ) = exp (t • X) := rfl

@[simp] theorem exponentialLine_zero (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L) : exponentialLine L X hX 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simp

theorem continuous_exponentialLine (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L) :
    Continuous (exponentialLine L X hX) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact exp_continuous.comp (continuous_id.smul continuous_const)

theorem exponentialLine_mem_identityComponent (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L) (t : ℝ) :
    exponentialLine L X hX t ∈ identityComponent L := by
  change exponentialLine L X hX t ∈ connectedComponent (1 : subgroup L)
  have ht : t ∈ connectedComponent (0 : ℝ) := by simp
  have h := (continuous_exponentialLine L X hX).mapsTo_connectedComponent 0 ht
  simpa only [exponentialLine_zero] using h

theorem exp_mem_componentMatrices_iff (X : Matrix n n ℂ) :
    (∀ t : ℝ, exp (t • X) ∈ componentMatrices L) ↔
      ∀ t : ℝ, exp (t • X) ∈ matrixCarrier L := by
  constructor
  · exact fun h t => componentMatrices_le L (h t)
  · intro h t
    exact (mem_componentMatrices L _).mpr
      ⟨exponentialLine L X h t, exponentialLine_mem_identityComponent L X h t, rfl⟩

end

end Math.MatrixLieGroupNormalizer
