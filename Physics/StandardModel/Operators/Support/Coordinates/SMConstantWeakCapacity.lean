import Math.RepresentationTheory.Exterior.BalancedExteriorWeights
import Math.RepresentationTheory.Exterior.ConstantPatternExterior
import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel

/-! A sharp constant-species weak cutoff on the actual exterior source.
No character extraction premise or numerical rank calculation is used. -/
namespace Physics.SMConstantWeakCapacity
set_option autoImplicit false
noncomputable section
open Math Representation BoundedTorusWeights SMWeakWeightBasis

/-- Capacity of the actual one-species field, kept as a basis cardinality. -/
def dimension (s : DeltaLOneSignedInput.Species) : ℕ := Fintype.card (FieldIndex s)

theorem field_dimension (s : DeltaLOneSignedInput.Species) :
    Module.finrank ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) =
      dimension s := Module.finrank_eq_card_basis (fieldBasis s)

theorem dimension_eq (s : DeltaLOneSignedInput.Species) :
    dimension s = (![36,18,18,12,6,36,18,18,12,6] : Fin 10 → ℕ) s :=
  (field_dimension s).symm.trans (ThreeGenerationFermionBound.species_dimension s)

def pattern (s : DeltaLOneSignedInput.Species) (n : ℕ) (_ : Fin n) := s

theorem field_weight_sum (s : DeltaLOneSignedInput.Species) :
    ∑ i : FieldIndex s, gaugeWeight s i.1.1 = 0 := by
  fin_cases s <;>
    simp [FieldIndex, GaugeIndex, gaugeWeight, weakWeight, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

theorem field_weight_bound (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) :
    -1 ≤ gaugeWeight s i.1.1 ∧ gaugeWeight s i.1.1 ≤ 1 := by
  have he := gauge_weight_bound s i.1.1
  have hc : doubletCount s ≤ 1 := by unfold doubletCount; split_ifs <;> omega
  constructor <;> omega

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def bound (s : DeltaLOneSignedInput.Species) (n : ℕ) : ℕ :=
  min n (dimension s-n)

theorem exterior_bounded (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    Bounded ((DeltaLOneSignedFields.field flavor s).exteriorPower n)
      (fullTorus (H := H)) (bound s n) := by
  let : LinearOrder (FieldIndex s) := IsWellOrder.linearOrder WellOrderingRel
  have he := BalancedExteriorWeights.bounded (DeltaLOneSignedFields.field flavor s)
    (fullTorus (H := H)) (fieldBasis s) (fun i => gaugeWeight s i.1.1)
    (field_basis_eigen flavor s) (field_weight_bound s) (field_weight_sum s) n
  simpa only [dimension, bound] using he

theorem source_bounded (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    Bounded (SMContentWeakBound.source flavor (pattern s n))
      (fullTorus (H := H)) (bound s n) :=
  bounded_of_surjective _ _ _
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s n).toIntertwiningMap
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s n).surjective
    _ (exterior_bounded flavor s n)

theorem local_high_zero (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (hm : bound s n < m)
    (f : InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern s n) m delta)) : f=0 := by
  exact BoundedHiggsSupport.high_zero
    (SMIntegralLocalWeights.source flavor (pattern s n))
    (SMHiggsConstituents.weakProjection.comp (MonoidHom.inl _ _))
    (SMHiggsConstituents.character.comp (MonoidHom.inl _ _))
    SMIntegralLocalWeights.weak (fun _ => rfl)
    (fun u => SMFiniteHiggsSupport.weak_character u)
    (bound s n) m delta (source_bounded flavor s n) hm f

theorem local_high_forbidden (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (hm : bound s n < m) : SelectionCriteria.Forbidden
      (InvariantCoefficientTransport.Invariants
        (SMIntegralLocalWeights.action flavor (pattern s n) m delta)) :=
  local_high_zero flavor s n m delta hm

theorem kernel_high_zero (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (hm : bound s n < m)
    (x : SMFullLocalKernel.Kernel flavor (pattern s n) m delta) : x=0 :=
  ((SelectionCriteria.ofEquiv (SMFullLocalKernel.coefficientEquiv flavor
    (pattern s n) m delta)).forbidden.mp
      (local_high_forbidden flavor s n m delta hm)) x

theorem kernel_high_finrank_zero (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (hm : bound s n < m) :
    Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern s n) m delta) = 0 := by
  let : Subsingleton (SMFullLocalKernel.Kernel flavor (pattern s n) m delta) :=
    ⟨fun x y => (kernel_high_zero flavor s n m delta hm x).trans
      (kernel_high_zero flavor s n m delta hm y).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end Physics.SMConstantWeakCapacity
