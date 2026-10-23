import Math.LinearAlgebra.Quaternion.QuaternionicSpectral
import Mathlib.Data.Nat.Find

/-! Complete paired orthonormal eigenbases from finite-dimensionality.
A maximal finite paired frame spans: otherwise its invariant orthogonal
complement supplies another eigenvector and its quaternionic partner. -/

set_option autoImplicit false

namespace Math.QuaternionicSpectral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

structure Frame (D : Data E) (n : ℕ) where
  vec : Fin n → E
  phase : Fin n → Circle
  orthonormal : Orthonormal ℂ vec
  cross : ∀ i j, inner ℂ (vec i) (D.q (vec j)) = 0
  eigen : ∀ i, D.t (vec i) = (phase i : ℂ) • vec i

namespace Frame

variable {D : Data E} {n : ℕ} (F : Frame D n)

def paired : Fin n ⊕ Fin n → E := Sum.elim F.vec (fun i => D.q (F.vec i))

theorem paired_orthonormal : Orthonormal ℂ F.paired := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [paired] using (orthonormal_iff_ite.mp F.orthonormal) i j
    | inr j => simpa [paired] using F.cross i j
  | inr i =>
    cases j with
    | inl j =>
      simpa [paired] using
        (inner_eq_zero_symm.mpr (F.cross j i))
    | inr j =>
      change inner ℂ (D.q (F.vec i)) (D.q (F.vec j)) = _
      rw [D.pairing, orthonormal_iff_ite.mp F.orthonormal i j]
      by_cases h : i = j <;> simp [h]

include F in
theorem size_bound [FiniteDimensional ℂ E] : 2 * n ≤ Module.finrank ℂ E := by
  have hh := F.paired_orthonormal.linearIndependent.fintype_card_le_finrank
  simpa [Fintype.card_sum, two_mul] using hh

def complement : Submodule ℂ E := (Submodule.span ℂ (Set.range F.paired))ᗮ

theorem mem_complement (w : E) : w ∈ F.complement ↔
    ∀ i, inner ℂ (F.vec i) w = 0 ∧ inner ℂ (D.q (F.vec i)) w = 0 := by
  constructor
  · intro hw i
    have h := (Submodule.mem_orthogonal _ w).mp hw
    exact ⟨h _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩),
      h _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)⟩
  · intro hw
    rw [complement, Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      cases i with
      | inl i => exact (hw i).1
      | inr i => exact (hw i).2
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [inner_smul_left, hx]

theorem q_mem_complement (w : E) (hw : w ∈ F.complement) : D.q w ∈ F.complement := by
  rw [F.mem_complement] at hw ⊢
  intro i
  constructor
  · rw [D.q_skew_pairing, (hw i).2, star_zero, neg_zero]
  · rw [D.pairing, (hw i).1, star_zero]

theorem t_mem_complement (w : E) (hw : w ∈ F.complement) : D.t w ∈ F.complement := by
  rw [F.mem_complement] at hw ⊢
  have aux (v : E) (z : Circle) (he : D.t v = (z : ℂ) • v)
      (hz : inner ℂ v w = 0) : inner ℂ v (D.t w) = 0 := by
    have hh := D.unitary v w
    rw [he, inner_smul_left, hz] at hh
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr (Circle.coe_ne_zero z))
  intro i
  exact ⟨aux _ _ (F.eigen i) (hw i).1, aux _ _ (D.q_eigen (F.eigen i)) (hw i).2⟩

def restricted : Data F.complement :=
  D.restrict F.complement F.t_mem_complement F.q_mem_complement

def extend (w : E) (z : Circle) (hn : ‖w‖ = 1)
    (he : D.t w = (z : ℂ) • w) (hw : w ∈ F.complement) : Frame D (n + 1) where
  vec := Fin.cons w F.vec
  phase := Fin.cons z F.phase
  orthonormal := by
    apply orthonormal_vecCons_iff.mpr
    exact ⟨hn, fun i => inner_eq_zero_symm.mpr ((F.mem_complement w).mp hw i).1,
      F.orthonormal⟩
  cross := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact D.q_orthogonal w
      · exact inner_eq_zero_symm.mpr ((F.mem_complement w).mp hw j).2
    · refine Fin.cases ?_ (fun j => ?_) j
      · change inner ℂ (F.vec i) (D.q w) = 0
        rw [D.q_skew_pairing, ((F.mem_complement w).mp hw i).2, star_zero, neg_zero]
      · exact F.cross i j
  eigen := by
    intro i
    exact Fin.cases he F.eigen i

end Frame

namespace Data

variable (D : Data E) [FiniteDimensional ℂ E]

def emptyFrame : Frame D 0 where
  vec := Fin.elim0
  phase := Fin.elim0
  orthonormal := Orthonormal.of_isEmpty _
  cross i := Fin.elim0 i
  eigen i := Fin.elim0 i

theorem exists_spanning_frame :
    ∃ (n : ℕ) (F : Frame D n), Submodule.span ℂ (Set.range F.paired) = ⊤ := by
  classical
  let P : ℕ → Prop := fun n => Nonempty (Frame D n)
  let m := Nat.findGreatest P (Module.finrank ℂ E)
  have hm : P m := Nat.findGreatest_spec (Nat.zero_le _) ⟨D.emptyFrame⟩
  obtain ⟨F⟩ := hm
  refine ⟨m, F, ?_⟩
  by_contra hs
  have hne : F.complement ≠ ⊥ := by
    intro hh
    exact hs (Submodule.orthogonal_eq_bot_iff.mp hh)
  let : Nontrivial F.complement := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨z, w, hn, he⟩ := F.restricted.exists_unit_eigenvector
  let F' : Frame D (m + 1) := F.extend w z hn (congrArg Subtype.val he) w.property
  have hb := F'.size_bound
  have hm' : m + 1 ≤ m := Nat.le_findGreatest (by omega) ⟨F'⟩
  omega

theorem exists_paired_eigenbasis :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n ⊕ Fin n) ℂ E) (z : Fin n → Circle),
      (∀ i, b (.inr i) = D.q (b (.inl i))) ∧
      (∀ i, D.t (b (.inl i)) = (z i : ℂ) • b (.inl i)) := by
  obtain ⟨n, F, hF⟩ := D.exists_spanning_frame
  let b := OrthonormalBasis.mk F.paired_orthonormal hF.ge
  refine ⟨n, b, F.phase, ?_, ?_⟩
  · intro i
    simp only [b, OrthonormalBasis.coe_mk, Frame.paired, Sum.elim_inl, Sum.elim_inr]
  · intro i
    simpa only [b, OrthonormalBasis.coe_mk, Frame.paired, Sum.elim_inl] using F.eigen i

include D in
theorem finrank_eq_twice : ∃ n : ℕ, Module.finrank ℂ E = 2 * n := by
  obtain ⟨n, b, _⟩ := D.exists_paired_eigenbasis
  exact ⟨n, by simpa [two_mul] using Module.finrank_eq_card_basis b.toBasis⟩

end Data

end

end Math.QuaternionicSpectral
