import Physics.StandardModel.Operators.Selection.CyclicResidualSelection
import Physics.StandardModel.Operators.Selection.FlavoredCyclicSelection
import Mathlib.Data.Finset.Card

/-! Reverse charge filtering for universal neutral-Higgs SM assignments. -/
namespace Physics.InverseCyclicSMCharges
set_option autoImplicit false
open Math Representation StandardBranchProtonObstruction

variable {k : ℕ} [NeZero k]

/-- All-left order Q, uc, dc, L, ec. -/
def chiral (q l : ZMod k) : Fin 5 → ZMod k := ![q,-q,-q,l,-l]
def YukawaNeutral (c : Fin 5 → ZMod k) : Prop :=
  c 0+c 1=0 ∧ c 0+c 2=0 ∧ c 3+c 4=0

omit [NeZero k] in
theorem yukawa_parametrization (c : Fin 5 → ZMod k) :
    YukawaNeutral c ↔ c = chiral (c 0) (c 3) := by
  constructor
  · rintro ⟨hu,hd,he⟩
    have hu' : c 1 = -c 0 := eq_neg_of_add_eq_zero_right hu
    have hd' : c 2 = -c 0 := eq_neg_of_add_eq_zero_right hd
    have he' : c 4 = -c 3 := eq_neg_of_add_eq_zero_right he
    ext i
    fin_cases i <;> simp [chiral, hu',hd',he']
  · intro h
    rw [h]
    simp [YukawaNeutral,chiral]

/-- Physical signed convention Q,uR,dR,L,eR; right-handed charges
are the negatives of the corresponding all-left conjugate charges. -/
def physical (q l : ZMod k) : CyclicResidualSelection.Charges k := ![q,q,q,l,l]

omit [NeZero k] in
theorem physical_dictionary (q l : ZMod k) :
    physical q l 0 = chiral q l 0 ∧ physical q l 1 = -chiral q l 1 ∧
    physical q l 2 = -chiral q l 2 ∧ physical q l 3 = chiral q l 3 ∧
    physical q l 4 = -chiral q l 4 := by simp [physical,chiral]

omit [NeZero k] in
theorem all_family_charges (q l : ZMod k) (i : Fin 4) :
    CyclicResidualSelection.familyCharge (physical q l) i = 3*q+l := by
  fin_cases i <;> simp [CyclicResidualSelection.familyCharge,physical] <;> ring

theorem bounded_four_forbidden_iff (q l : ZMod k) :
    SelectionCriteria.Forbidden (DeltaLOneSignedFields.Sector
      (CyclicResidualSelection.flavor (physical q l)) 1) ↔ 3*q+l ≠ 0 := by
  rw [CyclicResidualSelection.forbidden_total_iff]
  simp only [all_family_charges]
  constructor
  · intro h; exact h 0
  · intro h _; exact h

def universal (q l : ZMod k) (s : Fin 5) (_ : Fin 3) : ZMod k := physical q l s

/-- Actual three-generation coefficient input: neutrality supplies a DUQL
coordinate, so prohibition covering this bounded sector requires the filter. -/
theorem three_generation_necessary (q l : ZMod k)
    (hp : SelectionCriteria.Forbidden (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1)) :
    3*q+l ≠ 0 := by
  intro hz
  have hzero : FlavoredCyclicCoordinates.fourCharge
      (universal q l 2) (universal q l 1) (universal q l 0) (universal q l 3)
      ((0,0),(0,0)) = 0 := by
    simp [FlavoredCyclicCoordinates.fourCharge,universal,physical]
    linear_combination hz
  have hc : Nonempty (FlavoredCyclicSelection.DuqlIndex (fun _ : Fin 5 => Fin 3) (universal q l)) :=
    ⟨⟨((0,0),(0,0)),hzero⟩⟩
  obtain ⟨f,hf⟩ := (FlavoredCyclicSelection.allowed_total_iff
    (fun _ : Fin 5 => Fin 3) (universal q l)).mpr (Or.inl hc)
  exact hf (hp f)

omit [NeZero k] in
/-- Every typed QQUE flavor coordinate has the same charge under the
universal assignment, including repeated quark flavors. -/
theorem universal_qque_charge (q l : ZMod k)
    (p : Sym (Fin 3) 2 × (Fin 3 × Fin 3)) :
    FlavoredCyclicCoordinates.qqueCharge (universal q l 0)
      (universal q l 1) (universal q l 4) p = 3*q+l := by
  obtain ⟨f,hf⟩ := TauCeti.Sym.ofFn_surjective p.1
  rcases p with ⟨p,ue⟩
  dsimp at hf
  subst p
  simp [FlavoredCyclicCoordinates.qqueCharge,CyclicWeightCoordinates.symmetricCharge,
    universal,physical,TauCeti.Sym.coe_ofFn]
  ring

omit [NeZero k] in
/-- The QQQL dictionary includes symmetric, alternating and mixed Young
branches; no ordered triple is assumed to be an independent coefficient. -/
theorem universal_qqql_charge (q l : ZMod k)
    (p : Fin 3 × TripleFlavorCoordinates.Index 3) :
    QqqlDiagonalCoordinates.charge
      (universal q l 0 ∘ (Fintype.equivFin (Fin 3)).symm)
      (universal q l 3 ∘ (Fintype.equivFin (Fin 3)).symm) p = 3*q+l := by
  rcases p with ⟨i,p⟩
  rcases p with p | (p | (p | ⟨p,r⟩))
  all_goals
    change q+q+q+l = 3*q+l
    ring

theorem three_generation_sufficient (q l : ZMod k) (h : 3*q+l ≠ 0) :
    SelectionCriteria.Forbidden (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1) := by
  apply (FlavoredCyclicSelection.forbidden_total_iff
    (fun _ : Fin 5 => Fin 3) (universal q l)).mpr
  refine ⟨⟨?_⟩,⟨⟨?_⟩,⟨⟨?_⟩,⟨?_⟩⟩⟩⟩
  · rintro ⟨p,hp⟩
    apply h
    simpa [FlavoredCyclicCoordinates.fourCharge,universal,physical,show 3*q=q+q+q by ring,add_assoc] using hp
  · rintro ⟨p,hp⟩
    exact h ((universal_qque_charge q l p).symm.trans hp)
  · rintro ⟨p,hp⟩
    exact h ((universal_qqql_charge q l p).symm.trans hp)
  · rintro ⟨p,hp⟩
    apply h
    simpa [FlavoredCyclicCoordinates.fourCharge,universal,physical,show 3*q=q+q+q by ring,add_assoc] using hp

/-- Exact bounded coefficient criterion, not all-degree B1 protection. -/
theorem three_generation_forbidden_iff (q l : ZMod k) :
    SelectionCriteria.Forbidden (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1) ↔
      3*q+l ≠ 0 :=
  ⟨three_generation_necessary q l,three_generation_sufficient q l⟩

theorem three_generation_allowed_iff (q l : ZMod k) :
    SelectionCriteria.Allowed (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1) ↔
      3*q+l = 0 := by
  rw [← not_iff_not, ← SelectionCriteria.forbidden_iff_not_allowed,
    three_generation_forbidden_iff]

/-- This enumerates only the arithmetic filter, not protecting models. -/
def candidates (k : ℕ) : Finset (ZMod k × ZMod k) :=
  if h : k = 0 then ∅ else
    letI : NeZero k := ⟨h⟩
    Finset.univ.filter (fun x => 3*x.1+x.2 ≠ 0)

theorem mem_candidates (q l : ZMod k) :
    (q,l) ∈ candidates k ↔ 3*q+l ≠ 0 := by
  simp [candidates,NeZero.ne k]

/-- The finite arithmetic filter is now exact for this bounded coefficient
predicate. It remains merely necessary for a stronger all-degree request. -/
theorem candidate_iff_three_generation_forbidden (q l : ZMod k) :
    (q,l) ∈ candidates k ↔ SelectionCriteria.Forbidden (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1) :=
  (mem_candidates q l).trans (three_generation_forbidden_iff q l).symm

theorem not_candidate_iff_three_generation_allowed (q l : ZMod k) :
    (q,l) ∉ candidates k ↔ SelectionCriteria.Allowed (DeltaLOneSignedFields.Sector
      (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3) (universal q l)) 1) := by
  rw [mem_candidates,three_generation_allowed_iff]
  exact not_not

theorem counts : ∀ i : Fin 11,
    (candidates (i.val+2)).card = (i.val+2)*(i.val+1) := by
  decide +kernel

theorem initial_count : (∑ i : Fin 11, (i.val+2)^2) = 649 := by decide +kernel

theorem surviving_count : (∑ i : Fin 11, (candidates (i.val+2)).card) = 572 := by
  simp_rw [counts]
  decide +kernel

theorem selected_candidate : ((0,1) : ZMod 2 × ZMod 2) ∈ candidates 2 := by decide +kernel

theorem selected_least (q l : ZMod 2) (h : (q,l) ∈ candidates 2) :
    q.val = 0 → 1 ≤ l.val := by
  intro hq
  have hn := (mem_candidates q l).mp h
  have hq' : q = 0 := (ZMod.val_eq_zero q).mp hq
  by_contra hl
  have hl' : l = 0 := (ZMod.val_eq_zero l).mp (by omega)
  simp [hq',hl'] at hn
end Physics.InverseCyclicSMCharges
