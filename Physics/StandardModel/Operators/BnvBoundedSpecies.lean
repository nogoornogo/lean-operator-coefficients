import Physics.StandardModel.Operators.DeltaLOneSpeciesSupport

/-! Necessary arithmetic support for bounded matter/Higgs BNV coefficients.
This predicate is not a definition of gauge-invariant coefficients. -/
namespace GUT.BnvBoundedSpecies
set_option autoImplicit false

open DeltaLOneSpeciesSupport

structure Counts where
  fermions : DeltaLOneSpeciesSupport.Counts
  higgs : ℕ
  conjugateHiggs : ℕ
  deriving DecidableEq

def doubledDimension (n : Counts) : ℕ :=
  3 * slotCount n.fermions + 2 * (n.higgs + n.conjugateHiggs)

def hypercharge (n : Counts) : ℤ :=
  sixHypercharge n.fermions + 3 * n.higgs - 3 * n.conjugateHiggs

/-- Numerical necessary conditions for a positive-baryon invariant.
The parity of all fermions and of left Weyl slots are separate conditions. -/
def PositiveAdmissible (bound : ℕ) (n : Counts) : Prop :=
  doubledDimension n ≤ 2 * bound ∧
  0 < threeBaryonDegree n.fermions ∧
  threeBaryonDegree n.fermions % 3 = 0 ∧
  slotCount n.fermions % 2 = 0 ∧
  leftSlots n.fermions % 2 = 0 ∧ hypercharge n = 0

def dimSix (f : DeltaLOneSpeciesSupport.Counts) : Counts := ⟨f, 0, 0⟩
def uddAntiL : Counts := ⟨⟨0,1,2,0,0,0,0,0,1,0⟩, 0, 1⟩
def qqdAntiL : Counts := ⟨⟨2,0,1,0,0,0,0,0,1,0⟩, 0, 1⟩
def qddAntiE : Counts := ⟨⟨1,0,2,0,0,0,0,0,0,1⟩, 0, 1⟩
def dddAntiL : Counts := ⟨⟨0,0,3,0,0,0,0,0,1,0⟩, 1, 0⟩

def conjugate (n : Counts) : Counts :=
  ⟨⟨n.fermions.cq, n.fermions.cu, n.fermions.cd, n.fermions.cl, n.fermions.ce,
    n.fermions.q, n.fermions.u, n.fermions.d, n.fermions.l, n.fermions.e⟩,
    n.conjugateHiggs, n.higgs⟩

@[simp] theorem conjugate_conjugate (n : Counts) : conjugate (conjugate n) = n := by
  cases n; rfl

@[simp] theorem conjugate_dimension (n : Counts) :
    doubledDimension (conjugate n) = doubledDimension n := by
  simp only [doubledDimension, conjugate, slotCount]
  omega

@[simp] theorem conjugate_baryon (n : Counts) :
    threeBaryonDegree (conjugate n).fermions = -threeBaryonDegree n.fermions := by
  simp only [conjugate, threeBaryonDegree]
  ring

@[simp] theorem conjugate_hypercharge (n : Counts) :
    hypercharge (conjugate n) = -hypercharge n := by
  simp only [conjugate, hypercharge, sixHypercharge]
  ring

def Admissible (bound : ℕ) (n : Counts) : Prop :=
  doubledDimension n ≤ 2 * bound ∧
  threeBaryonDegree n.fermions ≠ 0 ∧
  threeBaryonDegree n.fermions % 3 = 0 ∧
  slotCount n.fermions % 2 = 0 ∧
  leftSlots n.fermions % 2 = 0 ∧ hypercharge n = 0

theorem admissible_iff_positive_or_conjugate (bound : ℕ) (n : Counts) :
    Admissible bound n ↔ PositiveAdmissible bound n ∨
      PositiveAdmissible bound (conjugate n) := by
  have hslots : slotCount (conjugate n).fermions = slotCount n.fermions := by
    simp only [conjugate, slotCount]; omega
  have hleft : leftSlots (conjugate n).fermions + leftSlots n.fermions =
      slotCount n.fermions := by
    simp only [conjugate, slotCount, leftSlots]; omega
  simp only [Admissible, PositiveAdmissible, conjugate_dimension,
    conjugate_baryon, conjugate_hypercharge, hslots]
  omega

theorem four_fermions_of_le_seven (n : Counts) (h : PositiveAdmissible 7 n) :
    slotCount n.fermions = 4 ∧ n.higgs + n.conjugateHiggs ≤ 1 ∧
      threeBaryonDegree n.fermions = 3 := by
  rcases n with ⟨⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩,h,ch⟩
  rcases h with ⟨hd, hb, ht, hp, _, _⟩
  dsimp only at hd hb ht hp ⊢
  have hn : slotCount ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩ ≤ 4 := by
    simp only [doubledDimension] at hd
    omega
  have hfour : slotCount ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩ = 4 := by
    have hthree : 3 ≤ threeBaryonDegree ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩ := by omega
    simp only [slotCount, threeBaryonDegree] at hn hp hthree ⊢
    omega
  refine ⟨hfour, ?_, ?_⟩
  · simp only [doubledDimension, hfour] at hd
    omega
  · simp only [slotCount] at hfour
    simp only [threeBaryonDegree] at hb ht ⊢
    omega

set_option maxHeartbeats 800000 in
theorem positive_le_seven_iff (n : Counts) : PositiveAdmissible 7 n ↔
    n = dimSix duql ∨ n = dimSix qque ∨ n = dimSix qqql ∨
    n = dimSix duue ∨ n = uddAntiL ∨ n = qqdAntiL ∨
    n = qddAntiE ∨ n = dddAntiL := by
  constructor
  · intro hn
    have hs := four_fermions_of_le_seven n hn
    rcases n with ⟨⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩,h,ch⟩
    simp only [PositiveAdmissible, doubledDimension, hypercharge, slotCount,
      threeBaryonDegree, leftSlots, sixHypercharge] at hn hs
    rcases hn with ⟨_, _, _, _, hleft, hy⟩
    rcases hs with ⟨hn, hscalar, hb⟩
    simp only [dimSix, duql, qque, qqql, duue, uddAntiL, qqdAntiL,
      qddAntiE, dddAntiL, Counts.mk.injEq, DeltaLOneSpeciesSupport.Counts.mk.injEq]
    have hc : cq = 0 ∧ cu = 0 ∧ cd = 0 := by
      clear hleft hy hscalar
      omega
    rcases hc with ⟨rfl,rfl,rfl⟩
    have hl : (l = 1 ∧ e = 0 ∧ cl = 0 ∧ ce = 0) ∨
        (l = 0 ∧ e = 1 ∧ cl = 0 ∧ ce = 0) ∨
        (l = 0 ∧ e = 0 ∧ cl = 1 ∧ ce = 0) ∨
        (l = 0 ∧ e = 0 ∧ cl = 0 ∧ ce = 1) := by
      clear hleft hy hscalar
      omega
    have hh : (h = 0 ∧ ch = 0) ∨ (h = 0 ∧ ch = 1) ∨ (h = 1 ∧ ch = 0) := by
      clear hleft hy hb
      omega
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      rcases hl with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
        ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
    all_goals
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num at *
    all_goals omega
  · intro hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [PositiveAdmissible, doubledDimension, hypercharge, slotCount,
        threeBaryonDegree, leftSlots, sixHypercharge, dimSix, duql, qque,
        qqql, duue, uddAntiL, qqdAntiL, qddAntiE, dddAntiL]

theorem no_positive_below_six (n : Counts) (bound : ℕ) (hb : bound < 6) :
    ¬ PositiveAdmissible bound n := by
  intro hn
  have hn7 : PositiveAdmissible 7 n := by
    rcases hn with ⟨hd, hrest⟩
    exact ⟨by omega, hrest⟩
  have hs := (four_fermions_of_le_seven n hn7).1
  have hd := hn.1
  simp only [doubledDimension, hs] at hd
  omega

/-- Every possible positive BNV type through eleven has four or six fermions.
This is only a support bound, not local invariant completeness. -/
theorem fermion_classes_le_eleven (n : Counts) (hn : PositiveAdmissible 11 n) :
    (slotCount n.fermions = 4 ∧ n.higgs + n.conjugateHiggs ≤ 5) ∨
    (slotCount n.fermions = 6 ∧ n.higgs + n.conjugateHiggs ≤ 2) := by
  rcases hn with ⟨hd, hb, ht, hp, _, _⟩
  have hle : slotCount n.fermions ≤ 7 := by
    unfold doubledDimension at hd
    omega
  have hthree : 3 ≤ threeBaryonDegree n.fermions := by omega
  have hbound : threeBaryonDegree n.fermions ≤ slotCount n.fermions := by
    simp only [threeBaryonDegree, slotCount]
    omega
  have hc : slotCount n.fermions = 4 ∨ slotCount n.fermions = 6 := by omega
  unfold doubledDimension at hd
  rcases hc with hc | hc
  · left; exact ⟨hc, by omega⟩
  · right; exact ⟨hc, by omega⟩

theorem baryon_classes_le_eleven (n : Counts) (hn : PositiveAdmissible 11 n) :
    threeBaryonDegree n.fermions = 3 ∨ threeBaryonDegree n.fermions = 6 := by
  have hs := fermion_classes_le_eleven n hn
  have hbound : threeBaryonDegree n.fermions ≤ slotCount n.fermions := by
    simp only [threeBaryonDegree, slotCount]
    omega
  have hb := hn.2.1
  have ht := hn.2.2.1
  rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩ <;> omega

def SevenFamily (n : Counts) : Prop :=
  n = dimSix duql ∨ n = dimSix qque ∨ n = dimSix qqql ∨
  n = dimSix duue ∨ n = uddAntiL ∨ n = qqdAntiL ∨
  n = qddAntiE ∨ n = dddAntiL

theorem admissible_le_seven_iff (n : Counts) :
    Admissible 7 n ↔ SevenFamily n ∨ SevenFamily (conjugate n) := by
  rw [admissible_iff_positive_or_conjugate,
    positive_le_seven_iff, positive_le_seven_iff]
  rfl

theorem positive_dimension_lepton_le_seven (n : Counts) (hn : PositiveAdmissible 7 n) :
    (doubledDimension n = 12 ∧ leptonDegree n.fermions = 1) ∨
    (doubledDimension n = 14 ∧ leptonDegree n.fermions = -1) := by
  rcases (positive_le_seven_iff n).mp hn with rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    norm_num [doubledDimension, leptonDegree, slotCount, dimSix,
      duql, qque, qqql, duue, uddAntiL, qqdAntiL, qddAntiE, dddAntiL]

@[simp] theorem conjugate_lepton (n : Counts) :
    leptonDegree (conjugate n).fermions = -leptonDegree n.fermions := by
  simp only [conjugate, leptonDegree]
  ring

theorem lepton_at_six (n : Counts) (hn : Admissible 6 n) :
    leptonDegree n.fermions = 1 ∨ leptonDegree n.fermions = -1 := by
  have h7 : Admissible 7 n := ⟨by have hd := hn.1; omega, hn.2⟩
  have hd := hn.1
  rcases (admissible_iff_positive_or_conjugate 7 n).mp h7 with hp | hp
  · have hs := positive_dimension_lepton_le_seven n hp
    omega
  · have hs := positive_dimension_lepton_le_seven (conjugate n) hp
    simp only [conjugate_dimension, conjugate_lepton] at hs
    omega

theorem no_bnv_below_six (n : Counts) (bound : ℕ) (hb : bound < 6) :
    ¬ Admissible bound n := by
  rw [admissible_iff_positive_or_conjugate]
  exact not_or.mpr ⟨no_positive_below_six n bound hb,
    no_positive_below_six (conjugate n) bound hb⟩

theorem baryon_bound_le_eleven (n : Counts) (hn : Admissible 11 n) :
    threeBaryonDegree n.fermions = 3 ∨ threeBaryonDegree n.fermions = 6 ∨
      threeBaryonDegree n.fermions = -3 ∨ threeBaryonDegree n.fermions = -6 := by
  rcases (admissible_iff_positive_or_conjugate 11 n).mp hn with h | h
  · rcases baryon_classes_le_eleven n h with h | h <;> simp [h]
  · have hb := baryon_classes_le_eleven (conjugate n) h
    simp only [conjugate_baryon] at hb
    omega

end GUT.BnvBoundedSpecies
