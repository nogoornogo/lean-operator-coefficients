import TauCeti.Topology.Homotopy.Path

/-! Simple-connectedness from two open simply-connected sets with
path-connected intersection. The argument uses a finite path subdivision. -/

set_option autoImplicit false
open scoped ContinuousMap unitInterval

namespace Math.SimplyConnectedUnion

noncomputable section

variable {X : Type*} [TopologicalSpace X]

theorem homotopic_of_mem {U : Set X} (hU : IsSimplyConnected U) {x y : X}
    (p q : Path x y) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) : p.Homotopic q := by
  let := hU.simplyConnectedSpace
  have hx : x ∈ U := by simpa using hp 0
  have hy : y ∈ U := by simpa using hp 1
  have h := SimplyConnectedSpace.paths_homotopic
    (p.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hp)
    (q.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hq)
  simpa using h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))

open Path.Homotopic.Quotient

/-- Local transport of path classes over an open cover extends to every path. -/
theorem transport_of_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {a : X} (C : (x : X) → Path.Homotopic.Quotient a x)
    (hlocal : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) →
      (C x).trans (mk p) = C y) {x y : X} (p : Path x y) :
    (C x).trans (mk p) = C y := by
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hseg⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (fun s _ => Set.mem_iUnion.mpr (hcover (p s)))
  have step (k : ℕ) :
      (C (p (t k))).trans (mk (p.subpath (t k) (t (k + 1)))) = C (p (t (k + 1))) := by
    obtain ⟨i, hi⟩ := hseg k
    apply hlocal i
    intro s
    have hs : p.subpath (t k) (t (k + 1)) s ∈ p '' Set.Icc (t k) (t (k + 1)) := by
      rw [← Path.range_subpath_of_le p _ _ (htmono (Nat.le_succ k))]
      exact Set.mem_range_self s
    rcases hs with ⟨s', hs', he⟩
    rw [← he]
    exact hi hs'
  have all (k : ℕ) :
      (C (p (t 0))).trans (mk (p.subpath (t 0) (t k))) = C (p (t k)) := by
    induction k with
    | zero => simp [Path.subpath_self]
    | succ k ih =>
      rw [← Path.Homotopic.mk_subpath_trans_mk_subpath p (t 0) (t k) (t (k + 1)),
        ← trans_assoc, ih]
      exact step k
  have hh := all N
  rw [ht0, hN N le_rfl] at hh
  have uncast {x' y' : X} (hx : x' = x) (hy : y' = y) :
      (C x').trans ((mk p).cast hx hy) = C y' → (C x).trans (mk p) = C y := by
    subst x'
    subst y'
    intro h
    simpa only [cast_rfl_rfl] using h
  apply uncast p.source p.target
  simpa only [subpath_zero_one] using hh

theorem simplyConnected_of_open_cover {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (sU : IsSimplyConnected U) (sV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) (hcover : U ∪ V = Set.univ) : SimplyConnectedSpace X := by
  classical
  have cover (x : X) : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := hcover ▸ Set.mem_univ x
    exact this
  obtain ⟨a, haU, haV⟩ := hUV.nonempty
  let PU (x : X) (hx : x ∈ U) : Path a x := (sU.isPathConnected.joinedIn a haU x hx).somePath
  let PV (x : X) (hx : x ∈ V) : Path a x := (sV.isPathConnected.joinedIn a haV x hx).somePath
  have memU (x : X) (hx : x ∈ U) (t : I) : PU x hx t ∈ U :=
    (sU.isPathConnected.joinedIn a haU x hx).somePath_mem t
  have memV (x : X) (hx : x ∈ V) (t : I) : PV x hx t ∈ V :=
    (sV.isPathConnected.joinedIn a haV x hx).somePath_mem t
  have agree (x : X) (hxU : x ∈ U) (hxV : x ∈ V) : mk (PU x hxU) = mk (PV x hxV) := by
    let r := (hUV.joinedIn a ⟨haU, haV⟩ x ⟨hxU, hxV⟩).somePath
    have hr (t : I) : r t ∈ U ∩ V :=
      (hUV.joinedIn a ⟨haU, haV⟩ x ⟨hxU, hxV⟩).somePath_mem t
    exact Quotient.sound ((homotopic_of_mem sU _ r (memU x hxU) (fun t => (hr t).1)).trans
      (homotopic_of_mem sV r _ (fun t => (hr t).2) (memV x hxV)))
  let C (x : X) : Path.Homotopic.Quotient a x :=
    if hx : x ∈ U then mk (PU x hx) else mk (PV x ((cover x).resolve_left hx))
  have cu (x : X) (hx : x ∈ U) : C x = mk (PU x hx) := by simp [C, hx]
  have cv (x : X) (hx : x ∈ V) : C x = mk (PV x hx) := by
    by_cases hxU : x ∈ U
    · rw [cu x hxU]; exact agree x hxU hx
    · simp [C, hxU]
  have localU {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U) :
      (C x).trans (mk p) = C y := by
    have hx : x ∈ U := by simpa using hp 0
    have hy : y ∈ U := by simpa using hp 1
    rw [cu x hx, cu y hy, ← mk_trans, eq]
    apply homotopic_of_mem sU _ _ _ (memU y hy)
    intro t
    simp only [Path.trans_apply]
    split_ifs
    · exact memU x hx _
    · exact hp _
  have localV {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ V) :
      (C x).trans (mk p) = C y := by
    have hx : x ∈ V := by simpa using hp 0
    have hy : y ∈ V := by simpa using hp 1
    rw [cv x hx, cv y hy, ← mk_trans, eq]
    apply homotopic_of_mem sV _ _ _ (memV y hy)
    intro t
    simp only [Path.trans_apply]
    split_ifs
    · exact memV x hx _
    · exact hp _
  have transport {x y : X} (p : Path x y) : (C x).trans (mk p) = C y := by
    apply transport_of_open_cover (fun b : Bool => if b then U else V) _ _ C _ p
    · intro b; cases b <;> assumption
    · intro x; rcases cover x with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · intro b; cases b
      · exact localV
      · exact localU
  apply simply_connected_iff_paths_homotopic'.mpr
  constructor
  · apply pathConnectedSpace_iff_univ.mpr
    rw [← hcover]
    exact sU.isPathConnected.union sV.isPathConnected ⟨a, haU, haV⟩
  · intro x y p q
    rw [← eq]
    have h : (C x).trans (mk p) = (C x).trans (mk q) := (transport p).trans (transport q).symm
    have hh := congrArg (fun r => (C x).symm.trans r) h
    simpa only [← trans_assoc, symm_trans, refl_trans] using hh

end

end Math.SimplyConnectedUnion
