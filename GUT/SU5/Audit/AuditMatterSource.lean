import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.SupportedTensors

open Physics

open Math

/-! Persistent source checks: finite generation mixing, repeated characters,
zero generations, incompatible within-multiplet actions, and actual tensors. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(5) source audit imports SU(6): {mod}"

namespace GUT.SU5.AuditMatterSource

noncomputable section

open MatterSource ResidualSectors SupportedFields SupportedTensors
open StandardSMGaugeTensor SMEpsilonTensor

def swap : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]⟩

theorem swap_squared : swap * swap = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [swap, Matrix.mul_apply, Fin.sum_univ_two]

def finiteSwap : ℤˣ →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun u := if u = 1 then 1 else swap
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> simp [swap_squared]

def mixingFactors : ℤˣ →* Factors 2 where
  toFun u i := match i with | .ten => finiteSwap u | .barFive => 1
  map_one' := by funext i; cases i <;> simp
  map_mul' u v := by funext i; cases i <;> simp

/-- A finite Abelian action that exchanges generations in the 10 and has a
repeated trivial character on both bar5 copies. -/
def mixingSource : OrdinaryAction ℤˣ 2 := ofFactors mixingFactors

theorem mixing_swaps (v : Generations 2) :
    representation mixingSource .ten (-1) v = WithLp.toLp 2 ![v 1, v 0] := by
  ext a
  fin_cases a <;>
    simp [representation_apply, sectorAction, mixingSource, mixingFactors, finiteSwap,
      swap, Fin.sum_univ_two]

theorem mixing_not_scalar :
    ¬ ∃ c : ℂ, ∀ v : Generations 2, representation mixingSource .ten (-1) v = c • v := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun v : Generations 2 => v 1) (hc (WithLp.toLp 2 ![1, 0]))
  rw [mixing_swaps] at h
  norm_num at h

theorem repeated_barFive_character : sector mixingSource .barFive 1 = ⊤ := by
  apply top_unique
  intro v _
  change ∀ h, representation mixingSource .barFive h v = ((1 : ℤˣ →* Circle) h : ℂ) • v
  intro h
  ext a
  simp [representation_apply, sectorAction, mixingSource, mixingFactors,
    Matrix.one_apply]

def oddCharacter : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> simp

theorem odd_mode : WithLp.toLp 2 (![1, -1] : Fin 2 → ℂ) ∈ sector mixingSource .ten oddCharacter := by
  intro h
  rcases Int.units_eq_one_or h with rfl | rfl
  · simp [oddCharacter]
  · rw [mixing_swaps]
    ext a
    fin_cases a <;> norm_num [oddCharacter]

theorem even_mode : WithLp.toLp 2 (![1, 1] : Fin 2 → ℂ) ∈ sector mixingSource .ten 1 := by
  intro h
  rcases Int.units_eq_one_or h with rfl | rfl
  · simp
  · rw [mixing_swaps]
    ext a
    fin_cases a <;> norm_num

theorem zero_generations_no_mode {H : Type*} [CommGroup H] (R : OrdinaryAction H 0) (i : Kind) :
    IsEmpty (Mode R i) := ⟨fun M => M.nonzero (Subsingleton.elim _ _)⟩

theorem trivial_sector {H : Type*} [CommGroup H] (n : ℕ) (i : Kind) :
    sector (ofFactors (1 : H →* Factors n)) i 1 = ⊤ := by
  apply top_unique
  intro v _ h
  ext a
  simp [representation_apply, sectorAction, Matrix.one_apply]

def oneCopy (x : Carrier .ten) : Space 1 := copy .ten (WithLp.toLp 2 ![1]) x

theorem oneCopy_component (x : Carrier .ten) : oneCopy x .ten 0 = x := by
  simp [oneCopy, copy]

theorem one_generation_scalar {H : Type*} [Group H] (R : OrdinaryAction H 1) (h : H)
    (x : Carrier .ten) :
    (R h).val.val (oneCopy x) .ten 0 = (sectorAction R .ten h).val 0 0 • x := by
  rw [action_eq_multiplicity]
  simp [oneCopy_component]

/-- An actual SU(5)-commuting action cannot fix one nonzero vector and
negate another in the same single copy of the irreducible 10. -/
theorem incompatible_within_ten {H : Type*} [Group H] (R : OrdinaryAction H 1) (h : H)
    (x y : Carrier .ten) (hx : x ≠ 0) (hy : y ≠ 0)
    (hfix : (R h).val.val (oneCopy x) = oneCopy x)
    (hneg : (R h).val.val (oneCopy y) = -oneCopy y) : False := by
  have h1 := congrArg (fun v : Space 1 => v .ten 0) hfix
  have h2 := congrArg (fun v : Space 1 => v .ten 0) hneg
  simp only [one_generation_scalar, oneCopy_component] at h1
  have hc1 : (sectorAction R .ten h).val 0 0 = 1 :=
    smul_left_injective ℂ hx (by simpa using h1)
  have hc2 : (sectorAction R .ten h).val 0 0 = -1 := by
    apply smul_left_injective ℂ hy
    simpa only [one_generation_scalar, PiLp.neg_apply, oneCopy_component, neg_one_smul] using h2
  norm_num [hc1] at hc2

def upVector : Carrier .ten := upIn (LinearMap.proj (0 : Fin 3))
def electronVector : Carrier .ten := electronIn (LinearMap.id : ℂ →ₗ[ℂ] ℂ)

theorem upVector_ne_zero : upVector ≠ 0 := by
  intro h
  have he := upIn_injective (h.trans (map_zero upIn).symm)
  have := LinearMap.congr_fun he (![1, 0, 0] : Color)
  norm_num at this

theorem electronVector_ne_zero : electronVector ≠ 0 := by
  intro h
  have he := electronIn_injective (h.trans (map_zero electronIn).symm)
  have := LinearMap.congr_fun he (1 : ℂ)
  norm_num at this

theorem no_opposite_up_electron {H : Type*} [Group H] (R : OrdinaryAction H 1) (h : H) :
    ¬ ((R h).val.val (oneCopy upVector) = oneCopy upVector ∧
      (R h).val.val (oneCopy electronVector) = -oneCopy electronVector) := by
  rintro ⟨hf, hn⟩
  exact incompatible_within_ten R h upVector electronVector upVector_ne_zero electronVector_ne_zero hf hn

theorem finite_mixing_supported_tensors :
    ∃ (k : StandardBranchProtonObstruction.Charges (FiniteAbelianChargeSectors.ChargeLabel ℤˣ))
      (S : Support mixingSource k),
      qqueTensor S ≠ 0 ∧ duqlTensor S ≠ 0 ∧
      (∀ g x, qqueTensor S (qqueAction S g x) = qqueTensor S x) ∧
      (∀ g x, duqlTensor S (duqlAction S g x) = duqlTensor S x) := by
  obtain ⟨k, S, _, hs⟩ := exists_supported_tensors mixingSource (by decide)
  exact ⟨k, S, hs⟩

#print axioms ExplicitMultiplicity.operator_exhausts
#print axioms ExplicitMultiplicity.unitaryEquiv
#print axioms centralizerEquiv
#print axioms constituent_jointlyContinuous
#print axioms gauge_jointlyContinuous
#print axioms gauge_unitary
#print axioms action_eq_multiplicity
#print axioms UnitaryCharacterSectors.exists_character_eigenvector
#print axioms UnitaryCharacterSectors.iSup_sector_eq_top
#print axioms UnitaryCharacterSectors.distinct_sectors_orthogonal
#print axioms sectors_exhaust
#print axioms copy_injective
#print axioms copy_gauge
#print axioms copy_residual
#print axioms exists_supported_compatible
#print axioms supported_neutral_signatures
#print axioms fieldRepresentation_val
#print axioms chargedDualEquiv
#print axioms rightSplit
#print axioms exists_supported_tensors
#print axioms mixingSource
#print axioms mixing_swaps
#print axioms mixing_not_scalar
#print axioms repeated_barFive_character
#print axioms odd_mode
#print axioms even_mode
#print axioms zero_generations_no_mode
#print axioms trivial_sector
#print axioms incompatible_within_ten
#print axioms no_opposite_up_electron
#print axioms finite_mixing_supported_tensors

end

end GUT.SU5.AuditMatterSource
