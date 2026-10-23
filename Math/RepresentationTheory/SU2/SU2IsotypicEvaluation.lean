import Math.RepresentationTheory.SU2.SU2FiniteBranching
import Math.RepresentationTheory.Decomposition.ProductFactorization
import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.RepresentationTheory.Characters.CompactHomSupport
import Math.RepresentationTheory.Decomposition.IrreducibleHomScalar
import Math.RepresentationTheory.Unitary.ContinuousConstructions

/-! Complete SU2 isotypic evaluation preserving every commuting group action.
All equal-label copies are combined into their actual Hom multiplicity space.
Dimensions are used symbolically, never evaluated at a closed source degree. -/
namespace Math.SU2IsotypicEvaluation
set_option autoImplicit false
noncomputable section
open Representation ProductFactorization SU2FiniteBranching
open scoped TensorProduct

abbrev model (m : ℕ) := (TauCeti.SU2.symPowerModel m).toRepresentation

theorem model_continuous (m : ℕ) : ContinuousRepresentationScope.IsJointlyContinuous (model m) := by
  apply ContinuousUnitaryConstructions.jointlyContinuous_of_orbit
  intro x
  exact continuous_clm_apply.mp (TauCeti.SU2.continuous_symPowerModel m) x

section Algebraic
variable {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
  (tau : Representation ℂ (TauCeti.SU2 × K) V) (N : ℕ)

abbrev Multiplicity (m : Fin (N+1)) := MultiplicitySpace tau (model m.val)
abbrev Piece (m : Fin (N+1)) :=
  EuclideanSpace ℂ (Fin (m.val+1)) ⊗[ℂ] Multiplicity tau N m
abbrev piece (m : Fin (N+1)) := ExternalTensorProduct.externalTprod (model m.val)
  (multiplicityRepresentation tau (model m.val))

def assemble : IntertwiningMap (FiniteBlockHom.action (piece tau N)) tau :=
  DistinctIrreducibleAssembly.assemble (piece tau N) tau
    (fun m => multiplicityEvaluation tau (model m.val))

@[simp] theorem assemble_single (m : Fin (N+1)) (x : Piece tau N m) :
    assemble tau N (Pi.single m x) = multiplicityEvaluation tau (model m.val) x :=
  DistinctIrreducibleAssembly.assemble_single _ _ _ m x

variable (C : Certificate (firstRestriction tau) N)

def copy (i : Fin C.decomposition.numberOfBlocks) : Multiplicity tau N (C.degree i) :=
  C.equivalence.toIntertwiningMap.comp
    ((FiniteBlockHom.inject C.summand i).comp
      (TauCeti.SU2.symPowerModelEquiv (C.degree i).val).symm.toIntertwiningMap)

include C in
theorem assemble_surjective : Function.Surjective (assemble tau N) := by
  classical
  intro x
  let v := C.equivalence.symm x
  let w := fun i => TauCeti.SU2.symPowerModelEquiv (C.degree i).val (v i)
  refine ⟨∑ i, Pi.single (C.degree i) (w i ⊗ₜ[ℂ] copy tau N C i), ?_⟩
  rw [map_sum]
  simp only [assemble_single, multiplicityEvaluation_apply_tmul]
  have he (i : Fin C.decomposition.numberOfBlocks) :
      copy tau N C i (w i) = C.equivalence (Pi.single i (v i)) := by
    change C.equivalence (Pi.single i
      ((TauCeti.SU2.symPowerModelEquiv (C.degree i).val).symm
        (TauCeti.SU2.symPowerModelEquiv (C.degree i).val (v i)))) = _
    rw [Representation.Equiv.symm_apply_apply]
  simp_rw [he]
  rw [← map_sum]
  have hv : (∑ i, Pi.single i (v i)) = v := by ext i; simp
  rw [hv]
  exact C.equivalence.apply_symm_apply x

end Algebraic

section Dimension
variable {K V : Type*} [Group K] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] (tau : Representation ℂ (TauCeti.SU2 × K) V) (N : ℕ)
  (C : Certificate (firstRestriction tau) N)

local instance blockFinite (i : Fin C.decomposition.numberOfBlocks) :
    FiniteDimensional ℂ (C.decomposition.block i) := FiniteDimensional.of_injective
  ((C.decomposition.block i).subtype.restrictScalars ℂ)
  (C.decomposition.block i).subtype_injective

private theorem block_hom_dimension (i : Fin C.decomposition.numberOfBlocks) (m : Fin (N+1)) :
    Module.finrank ℂ (IntertwiningMap (C.decomposition.blockRepresentation i) (model m.val)) =
      if C.degree i = m then 1 else 0 := by
  classical
  let := C.decomposition.blockRepresentation_isIrreducible i
  let := TauCeti.SU2.isIrreducible_symPowerModel m.val
  split_ifs with h
  · let e : Representation.Equiv (C.decomposition.blockRepresentation i) (model m.val) :=
      (C.blockEquiv i).symm.trans (by
        rw [h, WeakDoubletScalars.symmetricPower_eq]
        exact TauCeti.SU2.symPowerModelEquiv m.val)
    exact (IrreducibleHomScalar.equiv _ _ e).finrank_eq.symm.trans (by simp)
  · have hd : Module.finrank ℂ (C.decomposition.block i) ≠
        Module.finrank ℂ (EuclideanSpace ℂ (Fin (m.val+1))) := by
      rw [← (C.blockEquiv i).finrank_eq, TauCeti.SU2.finrank_symPower]
      simp only [finrank_euclideanSpace_fin]
      intro he
      exact h (Fin.ext (by omega))
    have hz (f : IntertwiningMap (C.decomposition.blockRepresentation i) (model m.val)) : f = 0 :=
      BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne hd f
    let : Subsingleton (IntertwiningMap (C.decomposition.blockRepresentation i) (model m.val)) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    exact Module.finrank_zero_of_subsingleton

theorem multiplicity_dimension
    (hr : ContinuousRepresentationScope.IsJointlyContinuous (firstRestriction tau))
    (m : Fin (N+1)) : Module.finrank ℂ (Multiplicity tau N m) =
      ∑ i, if C.degree i = m then 1 else 0 := by
  change Module.finrank ℂ (IntertwiningMap (model m.val) (firstRestriction tau)) = _
  rw [CompactHomSupport.dimension_symm _ _ (model_continuous m.val) hr,
    (FiniteConstituentSupport.homEquiv C.decomposition (model m.val)).finrank_eq,
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl (fun i _ => block_hom_dimension tau N C i m)

include C in
theorem dimension_eq (hr : ContinuousRepresentationScope.IsJointlyContinuous (firstRestriction tau)) :
    Module.finrank ℂ (∀ m : Fin (N+1), Piece tau N m) = Module.finrank ℂ V := by
  rw [Module.finrank_pi_fintype]
  simp_rw [Module.finrank_tensorProduct, finrank_euclideanSpace_fin,
    multiplicity_dimension tau N C hr, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ((C.degree i).val+1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [eq_comm]
    _ = ∑ i, Module.finrank ℂ (C.decomposition.block i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (C.blockEquiv i).finrank_eq, TauCeti.SU2.finrank_symPower]
    _ = _ := C.decomposition.sum_finrank

/-- Canonical multiplicities retain the complete commuting K action. -/
def equivalence (hr : ContinuousRepresentationScope.IsJointlyContinuous (firstRestriction tau)) :
    Representation.Equiv (FiniteBlockHom.action (piece tau N)) tau :=
  (assemble tau N).ofBijective
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (assemble tau N).toLinearMap) (dimension_eq tau N C hr)).mpr
        (assemble_surjective tau N C), assemble_surjective tau N C⟩

end Dimension
end
end Math.SU2IsotypicEvaluation
