import Physics.StandardModel.Operators.SMLowerHiggsSupport
import Physics.StandardModel.Operators.SMQ18Support

/-! All positive-Q original-Higgs support, without numerical multiplicities. -/
namespace GUT.SMQuarkAllHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy SMLowerGenerationSupport SMLowerHiggsSupport
open scoped TensorProduct

attribute [local irreducible] TopExteriorCauchy.map SymmetricCauchy.map
  SU2SymmetricEmbeddings.omegaPower

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
      WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup SMQ18Support.Field := inferInstance

def complementary : Representation.Equiv (SMQ18Support.rho.exteriorPower 24)
    (SMQ18Support.rho.exteriorPower 12).dual :=
  ComplementaryExteriorDuality.equiv SMQ18Support.rho SMQ18Support.field_det
    (exteriorPower.topEquiv (Module.finBasis ℂ SMQ18Support.Field))
    (by rw [SMQ18Support.field_dimension])

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

include flavor in
theorem twelve_coefficient (m : ℕ) (hm : m % 2=0) (hmax : m ≤ 12) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMQ18Support.rho.exteriorPower 12).tprod (weak.symmetricPower m))) := by
  apply (SMGenerationCoefficients.exterior_coefficient_iff flavor 0 12 m
    SMQ18Support.rho actual_quark).mpr
  obtain ⟨f,hf⟩ := SMGenerationSupport.quark_twelve m hm hmax
  let : Nontrivial (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      change 0 < Module.finrank ℂ (Sym[ℂ]^m (Fin 2 → ℂ))
      rw [TauCeti.SU2.finrank_symPower]; omega)
  refine ⟨f,?_⟩
  intro hz
  obtain ⟨x,hx⟩ := exists_ne (0 : Sym[ℂ]^m WeakDoubletScalars.Doublet)
  exact hx (hf (by rw [hz]; rfl))

include flavor in
theorem twenty_four_constituent (m : ℕ) (hm : m % 2=0) (hmax : m ≤ 12) :
    SelectionCriteria.Allowed (IntertwiningMap (weak.symmetricPower m)
      (SMQ18Support.rho.exteriorPower 24)) := by
  have hc := twelve_coefficient flavor m hm hmax
  have ht := (SelectionCriteria.allowed_equiv
    ((InvariantCoefficientTransport.alongEquiv (Representation.TensorProduct.comm
      (SMQ18Support.rho.exteriorPower 12) (weak.symmetricPower m))).trans
      (InvariantTensorCurry.equiv (weak.symmetricPower m)
        (SMQ18Support.rho.exteriorPower 12)))).mp hc
  exact (SelectionCriteria.allowed_equiv
    (InvariantTensorCurry.postcompose (weak.symmetricPower m)
      (SMQ18Support.rho.exteriorPower 12).dual complementary.symm)).mp ht

theorem restore_charge (n m : ℕ) (delta : ℤ) (hc : (n : ℤ)+3*delta=0)
    (h : SelectionCriteria.Allowed (IntertwiningMap (weak.symmetricPower m)
      (SMQ18Support.rho.exteriorPower n))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 0 n) m delta)) := by
  apply SMGenerationCoefficients.local_of_nonzero_constituent flavor 0 n m delta
    SMQ18Support.rho actual_quark
  · change SMContentWeakBound.hypercharge (pattern 0 n)+3*delta=0
    rw [quark_charge]; exact hc
  · exact h

theorem twenty_four_local (m : ℕ) (hm : m % 2=0) (hmax : m ≤ 12) (delta : ℤ)
    (hc : (24 : ℤ)+3*delta=0) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 0 24) m delta)) :=
  restore_charge flavor 24 m delta hc (twenty_four_constituent flavor m hm hmax)

theorem local_higgs_iff (n h d : ℕ) :
    LocalHiggs flavor (pattern 0 n) h d ↔ n % 2=0 ∧ n ≤ 24 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  constructor
  · rintro ⟨m,hm,ha⟩
    have hc := SMChargedKernelRank.local_charge flavor (pattern 0 n) m.val ((h : ℤ)-d) ha
    rw [quark_charge] at hc
    have hp : n % 2=0 := by
      by_contra hp
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMParityKernelRank.forbidden flavor (pattern 0 n) m.val ((h : ℤ)-d) hp) ha
    have hb : m.val ≤ SMConstantWeakCapacity.bound 0 n := by
      by_contra hb
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMConstantWeakCapacity.local_high_forbidden flavor 0 n m.val ((h : ℤ)-d)
          (by omega)) ha
    have hdim : SMConstantWeakCapacity.dimension 0=36 := by
      simpa using SMConstantWeakCapacity.dimension_eq 0
    simp only [SMConstantWeakCapacity.bound, hdim] at hb
    dsimp [BoundedHiggsSupport.Admissible] at hm
    exact ⟨hp,by omega,hc⟩
  · rintro ⟨hp,hmax,hc⟩
    by_cases hlo : n ≤ 18
    · exact (quark_lower_local_iff flavor n hlo h d).mpr ⟨hp,hc⟩
    · have hn : n=24 := by omega
      subst n
      refine ⟨⟨8,by rw [quark_bound]; omega⟩,?_,?_⟩
      · dsimp [BoundedHiggsSupport.Admissible]; omega
      · exact twenty_four_local flavor 8 (by omega) (by omega) ((h : ℤ)-d) hc

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
theorem original_ql_iff (n h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 0 n) h d) ↔
      n • q=0 ∧ n % 2=0 ∧ n ≤ 24 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  rw [ql_original_iff, quark_residual_charge, local_higgs_iff]

omit flavor in
theorem original_ql_forbidden (n h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 0 n) h d) ↔
      n • q ≠ 0 ∨ n % 2 ≠ 0 ∨ 24 < n ∨ (n : ℤ)+3*((h : ℤ)-d) ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_ql_iff q l n h d]
  simp only [not_and_or, not_le]

end
end GUT.SMQuarkAllHiggsSupport
