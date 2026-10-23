import GUT.SU5.Branching.ActualHyperchargeProfiles
import GUT.SU5.SelectionRules.ActualExoticMassBounds
import Math.RepresentationTheory.Characters.CharacterProducts

open Physics

namespace GUT.SU5.ActualFullFamilyIndex
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding InvariantWeylMass
open StandardSMGaugeTensor
open FortyHyperchargeExclusion ExoticHyperchargeBasis ActualHyperchargeProfiles
open scoped BigOperators
open CharacterProducts
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup Kernel := inferInstance
local instance : Module ℂ Kernel := inferInstance
local instance : AddCommGroup Fifty := inferInstance
local instance : Module ℂ Fifty := inferInstance

abbrev Counts := Fin 4 → ℕ
abbrev Source (p : Counts) := (Fin (p 0) → Ten) × ((Fin (p 1) → BarFive) ×
  ((Fin (p 2) → Module.Dual ℂ Kernel) × (Fin (p 3) → Fifty)))
def source (p : Counts) : Representation ℂ GaugeGroup (Source p) :=
  (FiniteSpectrum.copies (p 0) (ten.comp hom)).prod
    ((FiniteSpectrum.copies (p 1) (antifundamental.comp hom)).prod
      ((FiniteSpectrum.copies (p 2) forty).prod (FiniteSpectrum.copies (p 3) fifty)))
abbrev Fields (p q : Counts) := Source p × Module.Dual ℂ (Source q)
local instance (p : Counts) : FiniteDimensional ℂ (Source p) := inferInstance
local instance (p q : Counts) : FiniteDimensional ℂ (Fields p q) := inferInstance
def fields (p q : Counts) : Representation ℂ GaugeGroup (Fields p q) := (source p).prod (source q).dual

def profile (p : Counts) : CyclicHypercharge.Polynomial :=
  (p 0 : ℤ) • tenProfile + (p 1 : ℤ) • CyclicHypercharge.dual five +
    (p 2 : ℤ) • fortyProfile + (p 3 : ℤ) • fiftyProfile

def smGeneration : Representation ℂ GaugeGroup (Ten × BarFive) :=
  Representation.prod (ten.comp hom) (antifundamental.comp hom)
def smProfile : CyclicHypercharge.Polynomial := tenProfile + CyclicHypercharge.dual five

theorem bar_character (g : CyclicHypercharge.Group) :
    antifundamental.character (hom (1,1,CyclicHypercharge.circle g)) =
      CyclicHypercharge.eval (CyclicHypercharge.dual five) g := by
  change fundamental.dual.character _ = _
  rw [Representation.char_dual]
  have hh : (hom (1,1,CyclicHypercharge.circle g))⁻¹ = hom (1,1,CyclicHypercharge.circle g⁻¹) := by
    exact (map_inv hom (1,1,CyclicHypercharge.circle g)).symm.trans (congrArg hom (by simp))
  rw [hh, five_character]
  exact (CyclicHypercharge.eval_dual _ g).symm

theorem source_character (p : Counts) (g : CyclicHypercharge.Group) :
    (source p).character (1,1,CyclicHypercharge.circle g) = CyclicHypercharge.eval (profile p) g := by
  have h40 : forty.character (1,1,CyclicHypercharge.circle g) = CyclicHypercharge.eval fortyProfile g := by
    rw [forty_eq_actual_restriction]
    exact forty_character g
  have h50 : fifty.character (1,1,CyclicHypercharge.circle g) = CyclicHypercharge.eval fiftyProfile g :=
    fifty_character g
  simp only [source, prod_character, FiniteSpectrum.character_copies,
    profile, CyclicHypercharge.eval_add, CyclicHypercharge.eval_zsmul,
    Int.cast_natCast]
  have ht : Representation.character (ten.comp hom) (1,1,CyclicHypercharge.circle g) =
      CyclicHypercharge.eval tenProfile g := ten_character g
  have hb : Representation.character (antifundamental.comp hom) (1,1,CyclicHypercharge.circle g) =
      CyclicHypercharge.eval (CyclicHypercharge.dual five) g := bar_character g
  rw [ht, hb, h40, h50]
  ring

theorem field_character (p q : Counts) (g : CyclicHypercharge.Group) :
    (fields p q).character (1,1,CyclicHypercharge.circle g) =
      CyclicHypercharge.eval (profile p + CyclicHypercharge.dual (profile q)) g := by
  rw [fields, prod_character, Representation.char_dual,
    CyclicHypercharge.eval_add, CyclicHypercharge.eval_dual]
  have hh : ((1,1,CyclicHypercharge.circle g) : GaugeGroup)⁻¹ = (1,1,CyclicHypercharge.circle g⁻¹) := by simp
  rw [hh, source_character, source_character]

theorem sm_character (g : CyclicHypercharge.Group) :
    smGeneration.character (1,1,CyclicHypercharge.circle g) = CyclicHypercharge.eval smProfile g := by
  rw [smGeneration, prod_character]
  change ten.character (hom (1,1,CyclicHypercharge.circle g)) +
    antifundamental.character (hom (1,1,CyclicHypercharge.circle g)) = _
  rw [ten_character, bar_character]
  exact (CyclicHypercharge.eval_add _ _ g).symm

def dualIndex (p : Counts) : CyclicHypercharge.Polynomial := profile p - CyclicHypercharge.dual (profile p)

/-- A weaker character-level SM condition, also implied by an exact SM radical.
It is on the actual light representation, not an unverified UV profile. -/
def HasSMLightIndex (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ) : Prop :=
  ∀ g : CyclicHypercharge.Group,
    B.radical.toRepresentation.character (1,1,CyclicHypercharge.circle g) -
      B.radical.toRepresentation.dual.character (1,1,CyclicHypercharge.circle g) =
        (N : ℂ) * (CyclicHypercharge.eval smProfile g - CyclicHypercharge.eval smProfile g⁻¹)

theorem light_index_of_exact_sm (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ)
    (e : Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) :
    HasSMLightIndex p q B N := by
  intro g
  have hc := congrArg (fun c : GaugeGroup → ℂ => c (1,1,CyclicHypercharge.circle g))
    (Representation.char_iso e)
  have hi := congrArg (fun c : GaugeGroup → ℂ => c (1,1,CyclicHypercharge.circle g⁻¹))
    (Representation.char_iso e)
  simp only [FiniteSpectrum.character_copies, sm_character] at hc hi
  have hh : ((1,1,CyclicHypercharge.circle g) : GaugeGroup)⁻¹ = (1,1,CyclicHypercharge.circle g⁻¹) := by simp
  have hd := (Representation.char_dual (ρ := B.radical.toRepresentation)
    (1,1,CyclicHypercharge.circle g)).trans
      (congrArg B.radical.toRepresentation.character hh)
  have hdiff := congrArg₂ (·-·) hc (hd.trans hi)
  exact hdiff.trans (by ring)

theorem source_index_from_mass (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ)
    (h : HasSMLightIndex p q B N) :
    dualIndex p - dualIndex q = (N : ℤ) • (smProfile - CyclicHypercharge.dual smProfile) := by
  apply CyclicHypercharge.eval_injective
  intro g
  have hm := (B.radical_dual_character_eq (1,1,CyclicHypercharge.circle g)).symm.trans (h g)
  have hh : ((1,1,CyclicHypercharge.circle g) : GaugeGroup)⁻¹ = (1,1,CyclicHypercharge.circle g⁻¹) := by simp
  have hd := (Representation.char_dual (ρ := fields p q)
    (1,1,CyclicHypercharge.circle g)).trans
      ((congrArg (fields p q).character hh).trans (field_character p q g⁻¹))
  have hv := (congrArg₂ (·-·) (field_character p q g) hd).symm.trans hm
  simp only [dualIndex, CyclicHypercharge.eval_sub, CyclicHypercharge.eval_dual,
    CyclicHypercharge.eval_add, CyclicHypercharge.eval_zsmul, Int.cast_natCast] at hv ⊢
  have hg : (g⁻¹)⁻¹ = g := inv_inv g
  rw [hg] at hv
  linear_combination hv

def rows : Fin 4 → ZMod 31 := ![12,-9,6,-3]

def entryPoly : Fin 4 → CyclicHypercharge.Polynomial :=
  ![tenProfile, CyclicHypercharge.dual five, fortyProfile, fiftyProfile]
def table : Fin 4 → Fin 4 → ℤ := ![![0,0,1,0],![0,0,0,2],![0,2,8,0],![1,0,0,16]]

theorem row_table : ∀ r i : Fin 4,
    (entryPoly r - CyclicHypercharge.dual (entryPoly r)) (rows i) = table r i := by
  intro r i
  fin_cases r <;> fin_cases i
  all_goals dsimp only [entryPoly, table, rows]
  all_goals simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    simp only [
      five_coefficients, ten_coefficients, forty_coefficients, fifty_coefficients,
      CyclicHypercharge.dual_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
  all_goals decide +kernel

theorem index_sum (p : Counts) : dualIndex p =
    ∑ r : Fin 4, (p r : ℤ) • (entryPoly r - CyclicHypercharge.dual (entryPoly r)) := by
  ext k
  simp [dualIndex, profile, entryPoly, Fin.sum_univ_four, CyclicHypercharge.dual_apply,
    Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply]
  ring

theorem index_rows (p : Counts) :
    dualIndex p (rows 0) = (p 3 : ℤ) ∧
    dualIndex p (rows 1) = 2 * (p 2 : ℤ) ∧
    dualIndex p (rows 2) = (p 0 : ℤ) + 8 * (p 2 : ℤ) ∧
    dualIndex p (rows 3) = 2 * (p 1 : ℤ) + 16 * (p 3 : ℤ) := by
  have hr (i : Fin 4) : dualIndex p (rows i) = ∑ r : Fin 4, (p r : ℤ) * table r i := by
    rw [index_sum]
    simp only [Finset.sum_apply', Finsupp.smul_apply, row_table, smul_eq_mul]
  rw [hr 0, hr 1, hr 2, hr 3]
  simp [Fin.sum_univ_four, table, mul_comm]

theorem sm_index_rows :
    (smProfile - CyclicHypercharge.dual smProfile) (rows 0) = 0 ∧
    (smProfile - CyclicHypercharge.dual smProfile) (rows 1) = 0 ∧
    (smProfile - CyclicHypercharge.dual smProfile) (rows 2) = 1 ∧
    (smProfile - CyclicHypercharge.dual smProfile) (rows 3) = 2 := by
  have he : smProfile - CyclicHypercharge.dual smProfile =
      (entryPoly 0 - CyclicHypercharge.dual (entryPoly 0)) +
      (entryPoly 1 - CyclicHypercharge.dual (entryPoly 1)) := by
    ext k
    simp [smProfile, entryPoly, CyclicHypercharge.dual_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  rw [he]
  simp [Finsupp.add_apply, row_table, table]

/-- Necessary actual UV copy constraints from an arbitrary mass's light SM index.
No formal SM branching profile, mass normal form or maximal rank is a premise. -/
theorem net_constraints (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ)
    (h : HasSMLightIndex p q B N) :
    (p 0 : ℤ) - q 0 = N ∧ (p 1 : ℤ) - q 1 = N ∧ p 2 = q 2 ∧ p 3 = q 3 := by
  have he := source_index_from_mass p q B N h
  have hr (i : Fin 4) := congrArg (fun f : CyclicHypercharge.Polynomial => f (rows i)) he
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  simp only [Finsupp.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rw [sm_index_rows.1, mul_zero, Finsupp.sub_apply] at h0
  rw [sm_index_rows.2.1, mul_zero, Finsupp.sub_apply] at h1
  rw [sm_index_rows.2.2.1, mul_one, Finsupp.sub_apply] at h2
  rw [sm_index_rows.2.2.2, Finsupp.sub_apply] at h3
  rw [(index_rows p).1, (index_rows q).1] at h0
  rw [(index_rows p).2.1, (index_rows q).2.1] at h1
  rw [(index_rows p).2.2.1, (index_rows q).2.2.1] at h2
  rw [(index_rows p).2.2.2, (index_rows q).2.2.2] at h3
  omega

theorem net_constraints_of_exact_sm (p q : Counts) (B : SymmetricMass (fields p q)) (N : ℕ)
    (e : Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) :
    (p 0 : ℤ) - q 0 = N ∧ (p 1 : ℤ) - q 1 = N ∧ p 2 = q 2 ∧ p 3 = q 3 :=
  net_constraints p q B N (light_index_of_exact_sm p q B N e)

/-- A count-only exclusion applied before any mass matrix is selected. -/
theorem copy_constraint_prefilter (p q : Counts) (N : ℕ)
    (hbad : ¬ ((p 0 : ℤ)-q 0=N ∧ (p 1 : ℤ)-q 1=N ∧ p 2=q 2 ∧ p 3=q 3))
    (B : SymmetricMass (fields p q)) :
    ¬ Nonempty (Representation.Equiv B.radical.toRepresentation (FiniteSpectrum.copies N smGeneration)) := by
  rintro ⟨e⟩
  exact hbad (net_constraints_of_exact_sm p q B N e)

end
end GUT.SU5.ActualFullFamilyIndex
