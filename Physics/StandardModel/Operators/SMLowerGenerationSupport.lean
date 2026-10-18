import Physics.StandardModel.Operators.SMGenerationCoefficients
import Physics.StandardModel.Operators.SMChargedKernelRank
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Math.LinearAlgebra.SymmetricPowerLowDegree

/-! Nonzero actual coefficients for all proved lower-half generation degrees. -/
namespace GUT.SMLowerGenerationSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy

abbrev pattern := SMConstantWeakCapacity.pattern

theorem quark_charge (n : ℕ) : SMContentWeakBound.hypercharge (pattern 0 n) = n := by
  simp [SMContentWeakBound.hypercharge, pattern, SMConstantWeakCapacity.pattern,
    DeltaLOneSignedInput.hypercharge]

theorem lepton_charge (n : ℕ) : SMContentWeakBound.hypercharge (pattern 3 n) = -3*(n : ℤ) := by
  simp [SMContentWeakBound.hypercharge, pattern, SMConstantWeakCapacity.pattern,
    DeltaLOneSignedInput.hypercharge]
  ring

theorem quark_bound (n : ℕ) : SMContentWeakBound.bound (pattern 0 n) = n := by
  simp [SMContentWeakBound.bound, pattern, SMConstantWeakCapacity.pattern, SMWeakWeightBasis.doubletCount]

theorem lepton_bound (n : ℕ) : SMContentWeakBound.bound (pattern 3 n) = n := by
  simp [SMContentWeakBound.bound, pattern, SMConstantWeakCapacity.pattern, SMWeakWeightBasis.doubletCount]

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem vacuum_local (s : DeltaLOneSignedInput.Species) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern s 0) 0 0)) := by
  let rho : Representation ℂ SMGenerationCauchy.Group
      (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
    (SMCombinedCompactAction.field s).comp inclusion
  apply SMGenerationCoefficients.local_of_constituent flavor s 0 0 0 rho rfl
  · simp [SMContentWeakBound.hypercharge]
  · let e := (SymmetricPowerLowDegree.representationZeroEquiv weak).trans
      rho.exteriorPowerZeroEquiv.symm
    exact ⟨e.toIntertwiningMap,e.injective⟩

theorem quark_local (n m : ℕ) (hn : n=6 ∨ n=12 ∨ n=18)
    (hm : m % 2=0) (hmax : m ≤ n) (delta : ℤ) (hc : (n : ℤ)+3*delta=0) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 0 n) m delta)) := by
  apply SMGenerationCoefficients.local_of_constituent flavor 0 n m delta
    (generations quark) actual_quark
  · change SMContentWeakBound.hypercharge (pattern 0 n) + 3*delta = 0
    rw [quark_charge]; exact hc
  · rcases hn with rfl | rfl | rfl
    · exact SMGenerationSupport.quark_six m hm hmax
    · exact SMGenerationSupport.quark_twelve m hm hmax
    · exact SMGenerationSupport.quark_eighteen m hm hmax

theorem lepton_local (n m : ℕ) (hn : n=2 ∨ n=4 ∨ n=6)
    (hm : m % 2=0) (hmax : m ≤ n) (delta : ℤ) (hc : delta=(n : ℤ)) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 3 n) m delta)) := by
  apply SMGenerationCoefficients.local_of_constituent flavor 3 n m delta
    (generations lepton) actual_lepton
  · change SMContentWeakBound.hypercharge (pattern 3 n) + 3*delta = 0
    rw [lepton_charge, hc]; ring
  · rcases hn with rfl | rfl | rfl
    · exact SMGenerationSupport.lepton_two m hm hmax
    · exact SMGenerationSupport.lepton_four m hm hmax
    · exact SMGenerationSupport.lepton_six m hm hmax

theorem quark_kernel (n m : ℕ) (hn : n=6 ∨ n=12 ∨ n=18)
    (hm : m % 2=0) (hmax : m ≤ n) (delta : ℤ) (hc : (n : ℤ)+3*delta=0) :
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor (pattern 0 n) m delta) :=
  (SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor _ m delta)).mp
    (quark_local flavor n m hn hm hmax delta hc)

theorem lepton_kernel (n m : ℕ) (hn : n=2 ∨ n=4 ∨ n=6)
    (hm : m % 2=0) (hmax : m ≤ n) (delta : ℤ) (hc : delta=(n : ℤ)) :
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor (pattern 3 n) m delta) :=
  (SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor _ m delta)).mp
    (lepton_local flavor n m hn hm hmax delta hc)

end
end GUT.SMLowerGenerationSupport
