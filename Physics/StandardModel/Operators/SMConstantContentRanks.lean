import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMChargedKernelRank
import Physics.StandardModel.Operators.LLHHKernelRank
import Physics.StandardModel.Operators.SMParityKernelRank

/-! Numerical dimension and rank formulas for all constant-species contents. -/
namespace GUT.SMConstantContentRanks
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

def dimension (s : DeltaLOneSignedInput.Species) : ℕ := ![36,18,18,12,6,36,18,18,12,6] s
def pattern (s : DeltaLOneSignedInput.Species) (n : ℕ) (_ : Fin n) := s
def columns (s : DeltaLOneSignedInput.Species) (n m : ℕ) := (dimension s).choose n * (m+1)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)

local instance fieldFinite : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field, ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

theorem source_dimension : Module.finrank ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (pattern s n)) =
    (dimension s).choose n := by
  unfold pattern
  rw [← (ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) s n).finrank_eq,
    exteriorPower.finrank_eq, ThreeGenerationFermionBound.species_dimension]
  rfl

theorem carrier_dimension : Module.finrank ℂ
    (SMFullLocalKernel.Carrier flavor (pattern s n) m) = columns s n m := by
  change Module.finrank ℂ (_ ⊗[ℂ] Sym[ℂ]^m WeakDoubletScalars.Doublet) = _
  rw [Module.finrank_tensorProduct, source_dimension, SymmetricPower.finrank_eq]
  simp [WeakDoubletScalars.Doublet, Nat.multichoose_two, columns]

theorem charge : SMContentWeakBound.hypercharge (pattern s n) =
    (n : ℤ) * DeltaLOneSignedInput.hypercharge s := by
  simp [SMContentWeakBound.hypercharge, pattern]

theorem charged_rank (hc : (n : ℤ) * DeltaLOneSignedInput.hypercharge s + 3*delta ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern s n) m delta)) =
      columns s n m := by
  have h := SMChargedKernelRank.full_rank flavor (pattern s n) m delta (by rwa [charge])
  simpa only [Fintype.card_fin, carrier_dimension] using h

theorem above_capacity_rank (hn : dimension s < n) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern s n) m delta)) = 0 := by
  have hd : Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern s n) m) = 0 := by
    rw [carrier_dimension, columns, Nat.choose_eq_zero_of_lt hn, zero_mul]
  have he := LinearMap.finrank_range_le (SMFullLocalKernel.constraints flavor (pattern s n) m delta)
  have hb : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern s n) m)) → ℂ) =
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern s n) m) := by simp
  exact Nat.eq_zero_of_le_zero (he.trans_eq (hb.trans hd))

/-- Conservative executable classifier. `none` means unclassified, not forbidden. -/
def evaluate (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ) : Option ℕ :=
  if dimension s < n then some 0
  else if n % 2 ≠ 0 then some (columns s n m)
  else if (n : ℤ) * DeltaLOneSignedInput.hypercharge s + 3*delta ≠ 0 then some (columns s n m)
  else if s=3 ∧ n=2 ∧ m=2 ∧ delta=2 then some 192
  else none

def actualRank (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints
    LLHHKernelRank.flavor (pattern s n) m delta))

theorem fixed_above (hn : dimension s < n) : actualRank s n m delta = 0 :=
  above_capacity_rank LLHHKernelRank.flavor s n m delta hn

theorem fixed_odd (hn : n % 2 ≠ 0) : actualRank s n m delta = columns s n m :=
  (SMParityKernelRank.full_rank LLHHKernelRank.flavor (pattern s n) m delta hn).trans
    (carrier_dimension LLHHKernelRank.flavor s n m)

theorem fixed_charged (hc : (n : ℤ) * DeltaLOneSignedInput.hypercharge s + 3*delta ≠ 0) :
    actualRank s n m delta = columns s n m :=
  charged_rank LLHHKernelRank.flavor s n m delta hc

theorem fixed_llhh : actualRank 3 2 2 2 = 192 := LLHHKernelRank.rank

attribute [local irreducible] actualRank

theorem evaluate_sound {s : DeltaLOneSignedInput.Species} {n m : ℕ} {delta : ℤ} {r : ℕ}
    (he : evaluate s n m delta = some r) :
    actualRank s n m delta = r := by
  unfold evaluate at he
  split at he
  · cases he
    exact fixed_above s n m delta ‹_›
  · split at he
    · cases he
      exact fixed_odd s n m delta ‹_›
    · split at he
      · cases he
        exact fixed_charged s n m delta ‹_›
      · split at he
        · obtain ⟨rfl,rfl,rfl,rfl⟩ := ‹s=3 ∧ n=2 ∧ m=2 ∧ delta=2›
          cases he
          exact fixed_llhh
        · cases he

end
end GUT.SMConstantContentRanks
