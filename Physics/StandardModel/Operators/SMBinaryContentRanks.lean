import Math.RepresentationTheory.BinaryPatternExterior
import Math.RepresentationTheory.PatternMultiplicityEquiv
import Physics.StandardModel.Operators.SMConstantContentRanks

/-! Exact source and carrier dimensions for any two distinct SM species. -/
namespace GUT.SMBinaryContentRanks
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

abbrev pattern := BinaryPatternExterior.pattern (S := DeltaLOneSignedInput.Species)
def columns (s t : DeltaLOneSignedInput.Species) (n k m : ℕ) :=
  (SMConstantContentRanks.dimension s).choose n * (SMConstantContentRanks.dimension t).choose k * (m+1)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  (s t : DeltaLOneSignedInput.Species) (n k m : ℕ) (delta : ℤ)

local instance fieldFinite (a : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) a) := by
  fin_cases a <;> dsimp [DeltaLOneSignedFields.Field, ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

/-- The full supplied gauge, Weyl and residual action is preserved. -/
def sourceEquiv (hst : s ≠ t) :=
  BinaryPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s t n k hst

theorem source_dimension (hst : s ≠ t) : Module.finrank ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (pattern s t n k)) =
    (SMConstantContentRanks.dimension s).choose n * (SMConstantContentRanks.dimension t).choose k := by
  rw [BinaryPatternExterior.dimension (DeltaLOneSignedFields.field flavor) s t n k hst,
    ThreeGenerationFermionBound.species_dimension, ThreeGenerationFermionBound.species_dimension]
  rfl

theorem carrier_dimension (hst : s ≠ t) :
    Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern s t n k) m) = columns s t n k m := by
  change Module.finrank ℂ (_ ⊗[ℂ] Sym[ℂ]^m WeakDoubletScalars.Doublet) = _
  rw [Module.finrank_tensorProduct, source_dimension flavor s t n k hst, SymmetricPower.finrank_eq]
  simp [WeakDoubletScalars.Doublet, Nat.multichoose_two, columns]

theorem charge : SMContentWeakBound.hypercharge (pattern s t n k) =
    (n : ℤ) * DeltaLOneSignedInput.hypercharge s + (k : ℤ) * DeltaLOneSignedInput.hypercharge t := by
  simp [SMContentWeakBound.hypercharge, pattern, BinaryPatternExterior.pattern, Fin.sum_univ_add]

theorem rank_add_nullity (hst : s ≠ t) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern s t n k) m delta)) +
      Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern s t n k) m delta) = columns s t n k m := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (SMFullLocalKernel.constraints flavor (pattern s t n k) m delta)
  simpa only [SMFullLocalKernel.Kernel, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    carrier_dimension flavor s t n k m hst] using h

theorem charged_rank (hst : s ≠ t)
    (hc : (n : ℤ) * DeltaLOneSignedInput.hypercharge s +
      (k : ℤ) * DeltaLOneSignedInput.hypercharge t + 3*delta ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern s t n k) m delta)) =
      columns s t n k m := by
  have h := SMChargedKernelRank.full_rank flavor (pattern s t n k) m delta (by rwa [charge])
  simpa only [Fintype.card_fin, carrier_dimension flavor s t n k m hst] using h

theorem odd_rank (hst : s ≠ t) (hn : (n+k) % 2 ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor (pattern s t n k) m delta)) =
      columns s t n k m :=
  (SMParityKernelRank.full_rank flavor (pattern s t n k) m delta hn).trans
    (carrier_dimension flavor s t n k m hst)

theorem reordered_source_dimension (hst : s ≠ t) (p : Fin (n+k) → DeltaLOneSignedInput.Species)
    (hc : ∀ a, (Finset.univ.filter (fun i => p i = a)).card =
      (Finset.univ.filter (fun i => pattern s t n k i = a)).card) :
    Module.finrank ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) =
      (SMConstantContentRanks.dimension s).choose n * (SMConstantContentRanks.dimension t).choose k :=
  (PatternMultiplicityEquiv.equiv (DeltaLOneSignedFields.field flavor) p (pattern s t n k) hc).finrank_eq.trans
    (source_dimension flavor s t n k hst)

end
end GUT.SMBinaryContentRanks
