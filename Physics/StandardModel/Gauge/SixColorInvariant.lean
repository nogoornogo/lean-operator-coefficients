import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Tactic

open Math

/-!
# Six-color invariants: pairs and the three-term relation

Torus weights force each color to occur twice. Signed color permutations
identify the 90 balanced coordinates with the 15 partitions into three pairs.
One four-slot rotation supplies a common three-term relation. Ten applications
reconstruct the 15 values from five probes.
-/

namespace GUT.SixColorInvariant

set_option autoImplicit false
noncomputable section

open Matrix SMEpsilonTensor Math.SmallSpecialUnitary

abbrev Group := Matrix.specialUnitaryGroup (Fin 3) ℂ

abbrev Index := Fin 6 → Fin 3
abbrev Coefficient := MultilinearMap ℂ (fun _ : Fin 6 => Color) ℂ

def IsInvariant (f : Coefficient) : Prop :=
  ∀ g v, f (fun s => defining 3 g (v s)) = f v

def basisValue (f : Coefficient) (idx : Index) : ℂ :=
  f (fun s => colorBasis (idx s))

def IsBalanced (idx : Index) : Prop :=
  ∀ r : Fin 3, List.count r (List.ofFn idx) = 2

instance (idx : Index) : Decidable (IsBalanced idx) :=
  inferInstanceAs (Decidable (∀ r : Fin 3, List.count r (List.ofFn idx) = 2))

/-- Five independent products of color epsilon tensors. -/
def pairingValue (p : Fin 5) (v : Fin 6 → Color) : ℂ := match p with
  | 0 => eps3 (v 0) (v 1) (v 2) * eps3 (v 3) (v 4) (v 5)
  | 1 => eps3 (v 0) (v 1) (v 3) * eps3 (v 2) (v 4) (v 5)
  | 2 => eps3 (v 0) (v 1) (v 4) * eps3 (v 2) (v 3) (v 5)
  | 3 => eps3 (v 0) (v 2) (v 3) * eps3 (v 1) (v 4) (v 5)
  | 4 => eps3 (v 0) (v 2) (v 4) * eps3 (v 1) (v 3) (v 5)

private def phaseZero : Group :=
  ⟨!![-1, 0, 0; 0, Complex.I, 0; 0, 0, Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
    · simp [Matrix.det_fin_three]⟩

private def phaseOne : Group :=
  ⟨!![Complex.I, 0, 0; 0, -1, 0; 0, 0, Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
    · simp [Matrix.det_fin_three]⟩

private def phaseTwo : Group :=
  ⟨!![Complex.I, 0, 0; 0, Complex.I, 0; 0, 0, -1], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
    · simp [Matrix.det_fin_three]⟩

private def phaseEigen (r i : Fin 3) : ℂ :=
  if i = r then -1 else Complex.I

private theorem phase_basis (r i : Fin 3) :
    defining 3 (![phaseZero, phaseOne, phaseTwo] r) (colorBasis i) =
      phaseEigen r i • colorBasis i := by
  ext q
  fin_cases r <;> fin_cases i <;> fin_cases q <;>
    simp [defining, phaseZero, phaseOne, phaseTwo, phaseEigen,
      Matrix.toLin'_apply, Matrix.mulVec, colorBasis]

private theorem phase_constraint (f : Coefficient) (hf : IsInvariant f)
    (r : Fin 3) (idx : Index) :
    ((∏ s, phaseEigen r (idx s)) - 1) * basisValue f idx = 0 := by
  have h := hf (![phaseZero, phaseOne, phaseTwo] r) (fun s => colorBasis (idx s))
  simp only [phase_basis, f.map_smul_univ, smul_eq_mul] at h
  change (∏ s, phaseEigen r (idx s)) * basisValue f idx = basisValue f idx at h
  linear_combination h

private theorem phaseEigen_eq (r i : Fin 3) :
    phaseEigen r i = Complex.I * (if i = r then Complex.I else 1) := by
  by_cases h : i = r <;> simp [phaseEigen, h]

private theorem phaseEigen_prod (r : Fin 3) (xs : List (Fin 3)) :
    (xs.map (phaseEigen r)).prod =
      Complex.I ^ xs.length * Complex.I ^ xs.count r := by
  rw [show xs.map (phaseEigen r) =
      xs.map (fun i => Complex.I * (if i = r then Complex.I else 1)) by
        apply List.map_congr_left
        intro i hi
        exact phaseEigen_eq r i]
  rw [List.prod_map_mul]
  have hpow :
      (xs.map (fun i => if i = r then Complex.I else 1)).prod =
        Complex.I ^ xs.count r := by
    simpa using List.prod_map_eq_pow_single (l := xs) r
      (fun i => if i = r then Complex.I else 1) (by
        intro i hi hmem
        simp [hi])
  rw [hpow]
  simp

private theorem bad_count_of_not_balanced :
    ∀ idx : Index, ¬ IsBalanced idx →
      ∃ r : Fin 3, List.count r (List.ofFn idx) ≠ 2 ∧
        List.count r (List.ofFn idx) ≠ 6 := by
  decide +kernel

theorem basisValue_vanish (f : Coefficient) (hf : IsInvariant f)
    (idx : Index) (h : ¬ IsBalanced idx) : basisValue f idx = 0 := by
  obtain ⟨r, h₂, h₆⟩ := bad_count_of_not_balanced idx h
  have hp := phase_constraint f hf r idx
  have hm := phaseEigen_prod r (List.ofFn idx)
  rw [← List.ofFn_comp', List.prod_ofFn] at hm
  norm_num [pow_succ] at hm
  have hn : -(Complex.I ^ List.count r (List.ofFn idx)) - 1 ≠ 0 := by
    have hle : List.count r (List.ofFn idx) ≤ 6 := by
      simpa using (List.count_le_length (a := r) (l := List.ofFn idx))
    interval_cases hc : List.count r (List.ofFn idx)
    all_goals simp_all [pow_succ]
    all_goals norm_num [Complex.ext_iff]
  rw [hm] at hp
  exact (mul_eq_zero.mp hp).resolve_left hn

private def rotateZeroOne : Group :=
  ⟨!![(3 : ℂ) / 5, 4 / 5, 0; -4 / 5, 3 / 5, 0; 0, 0, 1], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, map_ofNat,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]⟩

private theorem rotateZeroOne_basis (i : Fin 3) :
    defining 3 rotateZeroOne (colorBasis i) = match i with
      | 0 => (3 / 5 : ℂ) • colorBasis 0 - (4 / 5 : ℂ) • colorBasis 1
      | 1 => (4 / 5 : ℂ) • colorBasis 0 + (3 / 5 : ℂ) • colorBasis 1
      | 2 => colorBasis 2 := by
  ext q
  fin_cases i <;> fin_cases q
  all_goals
    simp [defining, rotateZeroOne, Matrix.toLin'_apply, Matrix.mulVec,
      colorBasis, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff]
  ring

/-! Color names can be exchanged: the minus sign makes each exchange special
unitary, and its sixth power is one. -/

private def swap01 : Group :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]⟩

private def swap12 : Group :=
  ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]⟩

private theorem swap_basis (t : Fin 2) (i : Fin 3) :
    defining 3 (![swap01, swap12] t) (colorBasis i) =
      (-1 : ℂ) • colorBasis ((![Equiv.swap 0 1, Equiv.swap 1 2] t) i) := by
  ext q
  fin_cases t <;> fin_cases i <;> fin_cases q <;>
    simp [defining, swap01, swap12, colorBasis, Matrix.toLin'_apply,
      Matrix.mulVec, Equiv.swap_apply_def, Fin.ext_iff]

theorem basisValue_swap (f : Coefficient) (hf : IsInvariant f)
    (t : Fin 2) (idx : Index) :
    basisValue f (fun s => (![Equiv.swap 0 1, Equiv.swap 1 2] t) (idx s)) =
      basisValue f idx := by
  have h := hf (![swap01, swap12] t) (fun s => colorBasis (idx s))
  simp only [swap_basis, f.map_smul_univ, smul_eq_mul] at h
  norm_num [Fin.prod_univ_succ] at h
  exact h

private theorem sum_cons {n : ℕ} {α : Type*} [Fintype α]
    (h : (Fin (n+1) → α) → ℂ) :
    ∑ p, h p = ∑ a, ∑ q : Fin n → α, h (Matrix.vecCons a q) := by
  calc
    _ = ∑ p : α × (Fin n → α), h (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α)).symm h
        (fun p => h (Fin.cons p.1 p.2)) (by intro p; simp)
    _ = _ := Fintype.sum_prod_type _

private def rotationScalar (i : Fin 3) (t : Fin 2) : ℂ :=
  (![![(3:ℂ)/5, -4/5], ![4/5, 3/5], ![1,0]] i) t

private def rotationIndex (i : Fin 3) (t : Fin 2) : Fin 3 :=
  if i = 2 then 2 else t.castLE (by decide)

private theorem rotation_tuple (idx : Index) (p : Fin 6 → Fin 2) :
    (fun s => rotationIndex (idx s) (p s)) =
      ![rotationIndex (idx 0) (p 0), rotationIndex (idx 1) (p 1),
        rotationIndex (idx 2) (p 2), rotationIndex (idx 3) (p 3),
        rotationIndex (idx 4) (p 4), rotationIndex (idx 5) (p 5)] := by
  ext s
  fin_cases s <;> rfl

/-- A matrix action expands once by multilinearity. The binary index records
the two entries in each active column; the spectator's second entry is zero. -/
private theorem rotation_expand (f : Coefficient) (idx : Index) :
    f (fun s => defining 3 rotateZeroOne (colorBasis (idx s))) =
      ∑ p : Fin 6 → Fin 2, (∏ s, rotationScalar (idx s) (p s)) *
        basisValue f (fun s => rotationIndex (idx s) (p s)) := by
  have hc (i : Fin 3) : defining 3 rotateZeroOne (colorBasis i) =
      ∑ t : Fin 2, rotationScalar i t • colorBasis (rotationIndex i t) := by
    fin_cases i <;>
      simp [rotateZeroOne_basis, rotationScalar, rotationIndex, Fin.sum_univ_two,
        sub_eq_add_neg, neg_div, neg_smul]
  simp_rw [hc]
  rw [f.map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [basisValue, smul_eq_mul] using
    f.map_smul_univ (fun s => rotationScalar (idx s) (p s))
      (fun s => colorBasis (rotationIndex (idx s) (p s)))

/-- With one spectator pair fixed, the three pairings of the other four
positions sum to zero. This is the only color contraction relation needed. -/
theorem three_term (f : Coefficient) (hf : IsInvariant f) :
    basisValue f ![0,0,1,1,2,2] + basisValue f ![0,1,0,1,2,2] +
      basisValue f ![0,1,1,0,2,2] = 0 := by
  have h := hf rotateZeroOne (fun s => colorBasis ((![0,0,0,1,2,2] : Index) s))
  rw [rotation_expand] at h
  change _ = basisValue f ![0,0,0,1,2,2] at h
  simp only [sum_cons, Fin.sum_univ_two, Fintype.sum_unique] at h
  simp only [rotation_tuple] at h
  norm_num [rotationScalar, rotationIndex, Fin.prod_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
  simp [basisValue_vanish f hf, IsBalanced, List.ofFn_succ,
    Fin.forall_fin_succ] at h
  have h₁ := basisValue_swap f hf 0 ![1,1,0,0,2,2]
  have h₂ := basisValue_swap f hf 0 ![1,0,1,0,2,2]
  have h₃ := basisValue_swap f hf 0 ![1,0,0,1,2,2]
  rw [show (fun s => (![Equiv.swap 0 1, Equiv.swap 1 2] (0:Fin 2))
    ((![1,1,0,0,2,2] : Index) s)) = ![0,0,1,1,2,2] by decide] at h₁
  rw [show (fun s => (![Equiv.swap 0 1, Equiv.swap 1 2] (0:Fin 2))
    ((![1,0,1,0,2,2] : Index) s)) = ![0,1,0,1,2,2] by decide] at h₂
  rw [show (fun s => (![Equiv.swap 0 1, Equiv.swap 1 2] (0:Fin 2))
    ((![1,0,0,1,2,2] : Index) s)) = ![0,1,1,0,2,2] by decide] at h₃
  rw [← h₁, ← h₂, ← h₃] at h
  linear_combination (625 / 84 : ℂ) * h


/-- Relabeling is generated by the two adjacent color exchanges. -/
def relabel : List (Fin 2) → Fin 3 → Fin 3
  | [] => id
  | t :: ts => fun i => (![Equiv.swap 0 1, Equiv.swap 1 2] t) (relabel ts i)

theorem basisValue_relabel (f : Coefficient) (hf : IsInvariant f)
    (word : List (Fin 2)) (idx : Index) :
    basisValue f (fun s => relabel word (idx s)) = basisValue f idx := by
  induction word with
  | nil => rfl
  | cons t ts ih =>
    exact (basisValue_swap f hf t (fun s => relabel ts (idx s))).trans ih

/-- A balanced coordinate is a partition of six slots into three unordered
pairs. Color names are assigned in order of first occurrence. -/
def representative : Fin 15 → Index := ![
  ![0,0,1,1,2,2],
  ![0,0,1,2,1,2],
  ![0,0,1,2,2,1],
  ![0,1,0,1,2,2],
  ![0,1,0,2,1,2],
  ![0,1,0,2,2,1],
  ![0,1,1,0,2,2],
  ![0,1,1,2,0,2],
  ![0,1,1,2,2,0],
  ![0,1,2,0,1,2],
  ![0,1,2,0,2,1],
  ![0,1,2,1,0,2],
  ![0,1,2,1,2,0],
  ![0,1,2,2,0,1],
  ![0,1,2,2,1,0]]

private def colorWords : Fin 6 → List (Fin 2) :=
  ![[], [0], [1], [0,1], [1,0], [0,1,0]]

/-- Finite combinatorial coverage, without any coefficient values or field
arithmetic: every balanced tuple is one of the fifteen pair partitions. -/
private theorem representative_coverage :
    ∀ idx : Index, IsBalanced idx →
      ∃ r : Fin 15, ∃ p : Fin 6,
        idx = fun s => relabel (colorWords p) (representative r s) := by
  decide +kernel

/-- Invariance is preserved when the six slots are reordered. -/
theorem invariant_domDomCongr (f : Coefficient) (hf : IsInvariant f)
    (σ : Equiv.Perm (Fin 6)) : IsInvariant (f.domDomCongr σ) := by
  intro g v
  exact hf g (fun s => v (σ s))

/-- The same three-term relation holds for every placement of the spectator
pair. Slot permutations carry the single proved relation to each placement. -/
theorem three_term_permuted (f : Coefficient) (hf : IsInvariant f)
    (σ : Equiv.Perm (Fin 6)) :
    basisValue f (fun s => (![0,0,1,1,2,2] : Index) (σ s)) +
    basisValue f (fun s => (![0,1,0,1,2,2] : Index) (σ s)) +
    basisValue f (fun s => (![0,1,1,0,2,2] : Index) (σ s)) = 0 :=
  three_term (f.domDomCongr σ) (invariant_domDomCongr f hf σ)


/-- Ten spectator placements suffice to reconstruct the non-probe values. -/
private def slotOrder : Fin 10 → Fin 6 → Fin 6 := ![
  ![4,5,0,1,2,3],
  ![4,0,5,1,2,3],
  ![0,4,1,2,5,3],
  ![0,1,4,5,2,3],
  ![0,4,1,2,3,5],
  ![4,0,1,5,2,3],
  ![0,1,4,2,5,3],
  ![4,0,1,2,3,5],
  ![0,4,5,1,2,3],
  ![4,0,1,2,5,3]]

private theorem slotOrder_bijective : ∀ r, Function.Bijective (slotOrder r) := by
  decide +kernel

private def slotPermutation (r : Fin 10) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (slotOrder r) (slotOrder_bijective r)

private def relationTriple : Fin 10 → Fin 3 → Fin 15 := ![
  ![0,1,2],
  ![3,4,5],
  ![4,9,14],
  ![0,13,14],
  ![5,10,13],
  ![6,9,10],
  ![1,10,12],
  ![8,12,14],
  ![6,7,8],
  ![7,11,13]]

private def relationColor : Fin 10 → Fin 3 → Fin 6 := ![
  ![4,4,4],
  ![4,4,4],
  ![2,2,2],
  ![2,0,0],
  ![2,2,2],
  ![4,4,4],
  ![2,0,0],
  ![4,4,4],
  ![2,2,2],
  ![4,4,4]]

private def baseTriple : Fin 3 → Index :=
  ![![0,0,1,1,2,2], ![0,1,0,1,2,2], ![0,1,1,0,2,2]]

/-- This finite check verifies only that slot and color relabelings implement
the stated pair partitions. It does not verify any field-valued equation. -/
private theorem relation_indices : ∀ r k,
    (fun s => baseTriple k (slotOrder r s)) =
    (fun s => relabel (colorWords (relationColor r k))
      (representative (relationTriple r k) s)) := by
  decide +kernel

private theorem pair_relation (f : Coefficient) (hf : IsInvariant f) (r : Fin 10) :
    basisValue f (representative (relationTriple r 0)) +
    basisValue f (representative (relationTriple r 1)) +
    basisValue f (representative (relationTriple r 2)) = 0 := by
  have h := three_term_permuted f hf (slotPermutation r)
  change basisValue f (fun s => baseTriple 0 (slotOrder r s)) +
    basisValue f (fun s => baseTriple 1 (slotOrder r s)) +
    basisValue f (fun s => baseTriple 2 (slotOrder r s)) = 0 at h
  simp only [relation_indices, basisValue_relabel f hf] at h
  exact h

/-- Five evaluations determine every invariant coefficient. -/
theorem eq_zero_of_probes (f : Coefficient) (hf : IsInvariant f)
    (h0 : basisValue f (representative 0) = 0)
    (h1 : basisValue f (representative 1) = 0)
    (h3 : basisValue f (representative 3) = 0)
    (h4 : basisValue f (representative 4) = 0)
    (h9 : basisValue f (representative 9) = 0) : f = 0 := by
  have h2 : basisValue f (representative 2) = 0 := by
    have h := pair_relation f hf 0
    change basisValue f (representative 0) + basisValue f (representative 1) + basisValue f (representative 2) = 0 at h
    linear_combination h - h0 - h1
  have h5 : basisValue f (representative 5) = 0 := by
    have h := pair_relation f hf 1
    change basisValue f (representative 3) + basisValue f (representative 4) + basisValue f (representative 5) = 0 at h
    linear_combination h - h3 - h4
  have h14 : basisValue f (representative 14) = 0 := by
    have h := pair_relation f hf 2
    change basisValue f (representative 4) + basisValue f (representative 9) + basisValue f (representative 14) = 0 at h
    linear_combination h - h4 - h9
  have h13 : basisValue f (representative 13) = 0 := by
    have h := pair_relation f hf 3
    change basisValue f (representative 0) + basisValue f (representative 13) + basisValue f (representative 14) = 0 at h
    linear_combination h - h0 - h14
  have h10 : basisValue f (representative 10) = 0 := by
    have h := pair_relation f hf 4
    change basisValue f (representative 5) + basisValue f (representative 10) + basisValue f (representative 13) = 0 at h
    linear_combination h - h5 - h13
  have h6 : basisValue f (representative 6) = 0 := by
    have h := pair_relation f hf 5
    change basisValue f (representative 6) + basisValue f (representative 9) + basisValue f (representative 10) = 0 at h
    linear_combination h - h9 - h10
  have h12 : basisValue f (representative 12) = 0 := by
    have h := pair_relation f hf 6
    change basisValue f (representative 1) + basisValue f (representative 10) + basisValue f (representative 12) = 0 at h
    linear_combination h - h1 - h10
  have h8 : basisValue f (representative 8) = 0 := by
    have h := pair_relation f hf 7
    change basisValue f (representative 8) + basisValue f (representative 12) + basisValue f (representative 14) = 0 at h
    linear_combination h - h12 - h14
  have h7 : basisValue f (representative 7) = 0 := by
    have h := pair_relation f hf 8
    change basisValue f (representative 6) + basisValue f (representative 7) + basisValue f (representative 8) = 0 at h
    linear_combination h - h6 - h8
  have h11 : basisValue f (representative 11) = 0 := by
    have h := pair_relation f hf 9
    change basisValue f (representative 7) + basisValue f (representative 11) + basisValue f (representative 13) = 0 at h
    linear_combination h - h7 - h13
  have hr : ∀ r, basisValue f (representative r) = 0 := by
    intro r
    fin_cases r <;> assumption
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin 3))
  intro idx
  simp only [Pi.basisFun_apply, _root_.zero_apply]
  change basisValue f idx = 0
  by_cases hb : IsBalanced idx
  · obtain ⟨r, p, he⟩ := representative_coverage idx hb
    rw [he, basisValue_relabel f hf]
    exact hr r
  · exact basisValue_vanish f hf idx hb

/-- Each contraction is a multilinear map on the same six-slot domain. -/
def pairing (p : Fin 5) : Coefficient :=
  MultilinearMap.mk' (pairingValue p) (by
    intro v i a b
    fin_cases p <;> fin_cases i <;>
      simp [pairingValue, Function.update, eps3, Fin.ext_iff] <;> ring) (by
    intro v i c a
    fin_cases p <;> fin_cases i <;>
      simp [pairingValue, Function.update, eps3, smul_eq_mul, Fin.ext_iff] <;> ring)

@[simp] theorem pairing_apply (p : Fin 5) (v : Fin 6 → Color) :
    pairing p v = pairingValue p v := rfl

theorem pairing_invariant (p : Fin 5) : IsInvariant (pairing p) := by
  intro g v
  have hd : Matrix.det (g : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  have he (a b c : Color) :
      eps3 (defining 3 g a) (defining 3 g b) (defining 3 g c) = eps3 a b c := by
    simpa [defining, Matrix.toLin'_apply] using eps3_invariant _ hd a b c
  fin_cases p <;> simp only [pairing_apply, pairingValue, he]

/-- Reconstruction from five epsilon coefficients. -/
def reconstruct (c : Fin 5 → ℂ) : Coefficient := ∑ p, c p • pairing p

@[simp] theorem reconstruct_apply (c : Fin 5 → ℂ) (v : Fin 6 → Color) :
    reconstruct c v = ∑ p, c p * pairingValue p v := by
  simp [reconstruct, smul_eq_mul]

theorem reconstruct_invariant (c : Fin 5 → ℂ) : IsInvariant (reconstruct c) := by
  intro g v
  simp only [reconstruct_apply]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact pairing_invariant p g v

/-- The probe at 012012 reads the sum of coefficients 0 and 4; the other
four probes read one coefficient each. Subtracting the 001122 value in the
first coordinate gives the inverse of this triangular evaluation matrix. -/
def coordinates (f : Coefficient) : Fin 5 → ℂ := ![
  basisValue f (representative 9) - basisValue f (representative 0),
  basisValue f (representative 4), basisValue f (representative 3),
  basisValue f (representative 1), basisValue f (representative 0)]

theorem coordinates_reconstruct (c : Fin 5 → ℂ) :
    coordinates (reconstruct c) = c := by
  ext p
  fin_cases p <;>
    simp [coordinates, basisValue, representative, reconstruct_apply,
      Fin.sum_univ_succ, pairingValue, eps3, colorBasis]

theorem linearIndependent_pairing : LinearIndependent ℂ pairing := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h := congrArg coordinates hc
  change coordinates (reconstruct c) = coordinates 0 at h
  rw [coordinates_reconstruct] at h
  have hz : coordinates (0 : Coefficient) = 0 := by
    ext q
    fin_cases q <;> simp [coordinates, basisValue]
  rw [hz] at h
  exact congrFun h p

/-- Every invariant coefficient is reconstructed from its five probes. -/
theorem reconstruct_coordinates (f : Coefficient) (hf : IsInvariant f) :
    reconstruct (coordinates f) = f := by
  have hi : IsInvariant (f - reconstruct (coordinates f)) := by
    intro g v
    simp only [_root_.sub_apply, hf g v, reconstruct_invariant (coordinates f) g v]
  have hz := eq_zero_of_probes (f - reconstruct (coordinates f)) hi
  have he : f - reconstruct (coordinates f) = 0 := by
    apply hz <;>
      simp [basisValue, coordinates, representative, reconstruct_apply,
        Fin.sum_univ_succ, pairingValue, eps3, colorBasis]
  exact (sub_eq_zero.mp he).symm

/-- Existence and uniqueness refer to the full SU(3)-invariant space. -/
theorem existsUnique_pairing_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃! c : Fin 5 → ℂ, reconstruct c = f := by
  refine ⟨coordinates f, reconstruct_coordinates f hf, ?_⟩
  intro c hc
  rw [← hc, coordinates_reconstruct]

theorem exists_pairing_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃ c : Fin 5 → ℂ, ∀ v, f v = ∑ p, c p * pairingValue p v := by
  refine ⟨coordinates f, ?_⟩
  intro v
  exact congrArg (fun q : Coefficient => q v) (reconstruct_coordinates f hf).symm

/-- Equality of invariant coefficients can be checked at five probes. -/
theorem eq_of_coordinates {f g : Coefficient} (hf : IsInvariant f)
    (hg : IsInvariant g) (h : coordinates f = coordinates g) : f = g := by
  rw [← reconstruct_coordinates f hf, ← reconstruct_coordinates g hg, h]

/-- The intrinsic invariant space, rather than a contraction-defined image,
is equivalent to five arbitrary complex coefficients. -/
def invariantEquiv : {f : Coefficient // IsInvariant f} ≃ (Fin 5 → ℂ) where
  toFun f := coordinates f.val
  invFun c := ⟨reconstruct c, reconstruct_invariant c⟩
  left_inv f := Subtype.ext (reconstruct_coordinates f.val f.property)
  right_inv := coordinates_reconstruct

theorem basis_ext {f g : Coefficient}
    (h : ∀ idx, basisValue f idx = basisValue g idx) : f = g := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin 3))
  intro idx
  simpa only [basisValue, colorBasis, Pi.basisFun_apply] using h idx

end
end GUT.SixColorInvariant
