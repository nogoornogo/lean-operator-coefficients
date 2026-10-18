import Physics.StandardModel.Operators.ContentHiggsSupport

namespace GUT.OutsideFamilyHiggsTrials
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput ContentHiggsSupport
variable {k : ℕ} [NeZero k] (q l : ZMod k)

/-- Positive scalar-only control; it contains no fermions. -/
def emptyContent (_ : Fin 0 → Species) : Prop := True

def emptyCoefficient : FiniteSpeciesExterior.Coefficient
    (DeltaLOneSignedFields.field (flavor q l)) 0 where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.constOfIsEmpty ℂ _ (Fin 0) 1)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.alternatingMapLinearEquiv _
      ((DeltaLOneSignedFields.fullRepresentation (flavor q l)).exteriorPower 0 g
        (exteriorPower.ιMulti ℂ 0 v)) =
      exteriorPower.alternatingMapLinearEquiv _ (exteriorPower.ιMulti ℂ 0 v)
    rw [Representation.exteriorPower_apply_ιMulti]
    simp

theorem emptyCoefficient_nonzero : emptyCoefficient q l ≠ 0 := by
  intro hz
  have he := congrArg (fun f : FiniteSpeciesExterior.Coefficient
    (DeltaLOneSignedFields.field (flavor q l)) 0 =>
    f (exteriorPower.ιMulti ℂ 0 (fun j => Fin.elim0 j))) hz
  simp [emptyCoefficient] at he

theorem empty_seed (_ : (0 : ZMod k)=0) : SelectionCriteria.Allowed (SeedSpace q l emptyContent) := by
  refine ⟨⟨emptyCoefficient q l,?_⟩,?_⟩
  · intro p hp; exact False.elim (hp trivial)
  · intro hz; exact emptyCoefficient_nonzero q l (congrArg Subtype.val hz)

theorem scalar_only_allowed_iff (h a : ℕ) :
    SelectionCriteria.Allowed (Space q l emptyContent h a) ↔ h=a := by
  have hh := ContentHiggsSupport.allowed_iff q l emptyContent 0
    (by intro p hp; simp) (by intro p hp; simp) (empty_seed q l) h a
  simpa using hh

/-- An arithmetic-neutral example still forbidden by odd fermion degree. -/
def tripleQ (p : Fin 3 → Species) : Prop := ∀ j, p j=0

theorem tripleQ_hyper (p : Fin 3 → Species) (hp : tripleQ p) :
    ∑ j, hypercharge (p j)=3 := by
  have he : p=fun _ => 0 := funext hp
  rw [he]
  norm_num [hypercharge]

omit [NeZero k] in
theorem tripleQ_weight (p : Fin 3 → Species) (hp : tripleQ p) :
    ∑ j, charge q l (p j)=3*q := by
  have he : p=fun _ => 0 := funext hp
  rw [he]
  simp [charge, DuqlHiggsContent.signedCharge]

theorem tripleQ_forbidden (h a : ℕ) : SelectionCriteria.Forbidden (Space q l tripleQ h a) :=
  ContentHiggsSupport.odd_forbidden q l tripleQ h a (by decide)

theorem neutral_arithmetic_not_sufficient :
    (3 : ℤ)+3*0-3*1=0 ∧ (3 : ZMod k)*0=0 ∧
    SelectionCriteria.Forbidden (Space (k := k) 0 l tripleQ 0 1) :=
  ⟨by norm_num, by simp, tripleQ_forbidden 0 l 0 1⟩

/-- A genuine different fermion degree: two physical up and four down quarks. -/
def sixPattern : Fin 6 → Species := ![1,1,2,2,2,2]
def sixQuarks (p : Fin 6 → Species) : Prop :=
  ∃ e : Equiv.Perm (Fin 6), p ∘ e=sixPattern


theorem six_stable (p : Fin 6 → Species) (e : Equiv.Perm (Fin 6)) :
    sixQuarks (p ∘ e) ↔ sixQuarks p := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨e*f,?_⟩
    simpa [Function.comp_def, Equiv.Perm.mul_apply] using hf
  · rintro ⟨f,hf⟩
    refine ⟨e⁻¹*f,?_⟩
    simpa [Function.comp_def, Equiv.Perm.mul_apply] using hf

theorem six_hyper (p : Fin 6 → Species) (hp : sixQuarks p) :
    ∑ j, hypercharge (p j)=0 := by
  obtain ⟨e,he⟩ := hp
  have hh : (∑ j, hypercharge (p j))=∑ j, hypercharge (sixPattern j) := by
    rw [← he]
    exact (Fintype.sum_equiv e _ _ (by intro j; rfl)).symm
  rw [hh]
  norm_num [sixPattern, hypercharge, Fin.sum_univ_succ]

omit [NeZero k] in
theorem six_weight (p : Fin 6 → Species) (hp : sixQuarks p) :
    ∑ j, charge q l (p j)=6*q := by
  obtain ⟨e,he⟩ := hp
  have hh : (∑ j, charge q l (p j))=∑ j, charge q l (sixPattern j) := by
    rw [← he]
    exact (Fintype.sum_equiv e _ _ (by intro j; rfl)).symm
  rw [hh]
  simp [sixPattern, charge, DuqlHiggsContent.signedCharge, Fin.sum_univ_succ]
  ring

theorem six_necessary (h a : ℕ) (hf : SelectionCriteria.Allowed (Space q l sixQuarks h a)) :
    h=a ∧ 6*q=0 := by
  have hh := ContentHiggsSupport.necessary q l sixQuarks 0 (6*q) six_hyper (six_weight q l) h a hf
  exact ⟨by omega, hh.2⟩

theorem six_obstructed (h a : ℕ) (ho : h≠a ∨ 6*q≠0) :
    SelectionCriteria.Forbidden (Space q l sixQuarks h a) := by
  apply ContentHiggsSupport.obstructed q l sixQuarks 0 (6*q) six_hyper (six_weight q l)
  rcases ho with hh | hc
  · left; omega
  · exact Or.inr hc

/-- Conditional diagnostic: the actual six-quark seed is still an explicit obligation. -/
theorem six_iff_of_seed (seed : 6*q=0 → SelectionCriteria.Allowed (SeedSpace q l sixQuarks))
    (h a : ℕ) : SelectionCriteria.Allowed (Space q l sixQuarks h a) ↔ h=a ∧ 6*q=0 :=
  ContentHiggsSupport.allowed_iff q l sixQuarks (6*q) (six_weight q l) six_hyper seed h a
end
end GUT.OutsideFamilyHiggsTrials
