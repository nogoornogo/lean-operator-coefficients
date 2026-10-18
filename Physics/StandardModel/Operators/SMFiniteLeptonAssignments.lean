import Physics.StandardModel.Operators.SMFiniteLeptonSupport
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma

/-! Candidates and verdicts are defined inside Lean, directly from the domain
and the uniform finite support theorem. No external table or CSV is an input. -/
namespace GUT.SMFiniteLeptonAssignments
set_option autoImplicit false
open Math SMFiniteLeptonSupport

structure Row where
  k : ℕ
  q : ℕ
  l : ℕ
  b1Forbidden : Bool
  b2Forbidden : Bool
  deriving DecidableEq

def b1Check (r : Row) : Bool := decide
  (∀ L ∈ leptonRange 3, (3 : ZMod r.k)*r.q + (L : ZMod r.k)*r.l≠0)
def b2Check (r : Row) : Bool := decide
  (∀ L ∈ leptonRange 6, (6 : ZMod r.k)*r.q + (L : ZMod r.k)*r.l≠0)
def Correct (r : Row) : Prop := b1Check r=r.b1Forbidden ∧ b2Check r=r.b2Forbidden
instance (r : Row) : Decidable (Correct r) := by unfold Correct; infer_instance

/-- Natural representatives are enumerated once in lexicographic order. -/
def candidatePairs (k : ℕ) : List (ℕ × ℕ) :=
  ((List.range k).product (List.range k)).filter (fun p => (3*p.1+p.2)%k≠0)

theorem mem_candidatePairs (k q l : ℕ) :
    (q,l) ∈ candidatePairs k ↔ q<k ∧ l<k ∧ (3*q+l)%k≠0 := by
  simp [candidatePairs, and_assoc]

theorem candidatePairs_nodup (k : ℕ) : (candidatePairs k).Nodup := by
  have h : (List.range k).Nodup := List.nodup_range
  exact (h.product h).filter _

/-- The flags are calculated from the proved support criterion, not supplied. -/
def classify (k q l : ℕ) : Row :=
  let r : Row := ⟨k,q,l,false,false⟩
  ⟨k,q,l,b1Check r,b2Check r⟩

theorem classify_correct (k q l : ℕ) : Correct (classify k q l) := by
  exact ⟨rfl,rfl⟩

def batches (i : Fin 11) : List Row :=
  (candidatePairs (i.val+2)).map (fun p => classify (i.val+2) p.1 p.2)

theorem all_correct : ∀ i, ∀ r ∈ batches i, Correct r := by
  intro i r hr
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  exact classify_correct _ _ _

theorem batch_modulus (i : Fin 11) (r : Row) (hr : r ∈ batches i) : r.k=i.val+2 := by
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  rfl

theorem all_domain : ∀ i, ∀ r ∈ batches i,
    2≤r.k ∧ r.k≤12 ∧ r.q<r.k ∧ r.l<r.k ∧ (3*r.q+r.l)%r.k≠0 := by
  intro i r hr
  obtain ⟨⟨q,l⟩,hp,rfl⟩ := List.mem_map.mp hr
  have hp := (mem_candidatePairs _ q l).mp hp
  have hi := i.isLt
  change 2 ≤ i.val+2 ∧ i.val+2 ≤ 12 ∧
    q < i.val+2 ∧ l < i.val+2 ∧ (3*q+l)%(i.val+2) ≠ 0
  exact ⟨by omega,by omega,hp⟩

/-- Assignment identity ignores the derived flags. -/
def key (r : Row) : ℕ × ℕ × ℕ := (r.k,r.q,r.l)

def rows : List Row := (List.finRange 11).flatMap batches

def keys : List (ℕ × ℕ × ℕ) :=
  (List.finRange 11).flatMap (fun i =>
    (candidatePairs (i.val+2)).map (fun p => (i.val+2,p.1,p.2)))

theorem keys_eq : rows.map key = keys := by
  simp only [rows, keys, List.map_flatMap, batches, List.map_map, Function.comp_def,
    key, classify]

theorem keys_nodup : keys.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact (candidatePairs_nodup _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange 11).imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hi hj
    obtain ⟨p,_,hp⟩ := List.mem_map.mp hi
    obtain ⟨q,_,hq⟩ := List.mem_map.mp hj
    have he := congrArg Prod.fst (hp.trans hq.symm)
    exact hij (Fin.ext (by simpa using he))

/-- Exact domain coverage, in both directions, without a supplied table. -/
theorem mem_keys (k q l : ℕ) : (k,q,l) ∈ keys ↔
    2 ≤ k ∧ k ≤ 12 ∧ q < k ∧ l < k ∧ (3*q+l)%k ≠ 0 := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp h
    obtain ⟨⟨q',l'⟩,hp,he⟩ := List.mem_map.mp hi
    have hk := congrArg Prod.fst he
    have hq := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) he
    have hl := congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) he
    have hd := (mem_candidatePairs _ q' l').mp hp
    dsimp only at hk hq hl
    subst k; subst q; subst l
    exact ⟨by omega,by have := i.isLt; omega,hd⟩
  · rintro ⟨hk,hk',hq,hl,hcharge⟩
    let i : Fin 11 := ⟨k-2,by omega⟩
    have he : i.val+2=k := by dsimp [i]; omega
    apply List.mem_flatMap.mpr
    refine ⟨i,by simp,?_⟩
    apply List.mem_map.mpr
    refine ⟨(q,l),?_,?_⟩
    · rw [he]
      exact (mem_candidatePairs k q l).mpr ⟨hq,hl,hcharge⟩
    · simp only [he]

/-- Each admissible natural triple has exactly one enumerated identity. -/
theorem unique_coverage (k q l : ℕ)
    (hd : 2 ≤ k ∧ k ≤ 12 ∧ q < k ∧ l < k ∧ (3*q+l)%k ≠ 0) :
    keys.count (k,q,l)=1 :=
  List.count_eq_one_of_mem keys_nodup ((mem_keys k q l).mpr hd)

theorem rows_nodup : rows.Nodup := by
  apply List.Nodup.of_map key
  rw [keys_eq]
  exact keys_nodup

theorem mem_rows_key (k q l : ℕ) :
    (∃ r ∈ rows, key r=(k,q,l)) ↔
      2 ≤ k ∧ k ≤ 12 ∧ q < k ∧ l < k ∧ (3*q+l)%k ≠ 0 := by
  rw [← mem_keys k q l, ← keys_eq, List.mem_map]

theorem row_count : (∑ i, (batches i).length)=572 := by decide +kernel

theorem rows_length : rows.length=572 := by decide +kernel

theorem keys_length : keys.length=572 := by rw [← keys_eq, List.length_map, rows_length]

/-- Aggregate counts of disjoint, exhaustive flag classes. -/
def classCount (f1 f2 : Bool) : ℕ :=
  ∑ i, ((batches i).filter (fun r => r.b1Forbidden==f1 && r.b2Forbidden==f2)).length

theorem classCount_rows (f1 f2 : Bool) : classCount f1 f2 =
    (rows.filter (fun r => r.b1Forbidden==f1 && r.b2Forbidden==f2)).length := by
  simp only [classCount, rows, List.filter_flatMap, List.length_flatMap, Fin.sum_univ_def]

theorem partition_counts :
    classCount false false=326 ∧ classCount true false=144 ∧
    classCount true true=102 ∧ classCount false true=0 := by
  decide +kernel

theorem b1_forbidden_count : classCount true false + classCount true true=246 := by
  obtain ⟨_,h1,h2,_⟩ := partition_counts
  omega

theorem b2_allowed_count : classCount false false + classCount true false=470 := by
  obtain ⟨h1,h2,_,_⟩ := partition_counts
  omega

theorem b1_allowed_count : classCount false false + classCount false true=326 := by
  obtain ⟨h1,_,_,h2⟩ := partition_counts
  omega

theorem b2_forbidden_count : classCount false true + classCount true true=102 := by
  obtain ⟨_,_,h1,h2⟩ := partition_counts
  omega

theorem b1_forbidden_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMQLPatternRequests.OriginalForbidden (r.q : ZMod r.k) r.l
      (fun c => c.1.natAbs=3) ↔ r.b1Forbidden=true := by
  rw [SMFiniteLeptonSupport.original_forbidden_iff _ _ 3 (Or.inl rfl)]
  rw [← (all_correct i r hr).1]
  simp [b1Check]

theorem b2_forbidden_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMQLPatternRequests.OriginalForbidden (r.q : ZMod r.k) r.l
      (fun c => c.1.natAbs=6) ↔ r.b2Forbidden=true := by
  rw [SMFiniteLeptonSupport.original_forbidden_iff _ _ 6 (Or.inr rfl)]
  rw [← (all_correct i r hr).2]
  simp [b2Check]

theorem allowed_not_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=b) ↔
      ¬SMQLPatternRequests.OriginalForbidden q l (fun c => c.1.natAbs=b) := by
  classical
  rw [← SMQLPatternRequests.forbidden_iff_original,
    SelectionCriteria.forbidden_iff_not_allowed, SMQLPatternRequests.allowed_iff_original]
  simp only [not_not]

theorem b1_allowed_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l
      (fun c => c.1.natAbs=3) ↔ r.b1Forbidden=false := by
  rw [allowed_not_forbidden, b1_forbidden_iff i r hr]
  cases r.b1Forbidden <;> decide

theorem b2_allowed_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l
      (fun c => c.1.natAbs=6) ↔ r.b2Forbidden=false := by
  rw [allowed_not_forbidden, b2_forbidden_iff i r hr]
  cases r.b2Forbidden <;> decide

theorem request_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMQLPatternRequests.Satisfies (r.q : ZMod r.k) r.l
      SMQLPatternRequests.b1ForbiddenB2Allowed ↔
        r.b1Forbidden=true ∧ r.b2Forbidden=false := by
  rw [SMQLPatternRequests.b1_b2_original_iff]
  exact and_congr (b1_forbidden_iff i r hr) (b2_allowed_iff i r hr)

/-- Semantic meaning of a counted class, on the original coefficient spaces. -/
def OriginalClass (r : Row) [NeZero r.k] (f1 f2 : Bool) : Prop :=
  (if f1 then SMQLPatternRequests.OriginalForbidden (r.q : ZMod r.k) r.l (fun c => c.1.natAbs=3)
    else SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l (fun c => c.1.natAbs=3)) ∧
  (if f2 then SMQLPatternRequests.OriginalForbidden (r.q : ZMod r.k) r.l (fun c => c.1.natAbs=6)
    else SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l (fun c => c.1.natAbs=6))

theorem class_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) (f1 f2 : Bool) :
    OriginalClass r f1 f2 ↔ r.b1Forbidden=f1 ∧ r.b2Forbidden=f2 := by
  cases f1 <;> cases f2 <;>
    simp only [OriginalClass, Bool.false_eq_true, ite_false, ite_true] <;>
    exact and_congr (by first | exact b1_allowed_iff i r hr | exact b1_forbidden_iff i r hr)
      (by first | exact b2_allowed_iff i r hr | exact b2_forbidden_iff i r hr)

end GUT.SMFiniteLeptonAssignments
