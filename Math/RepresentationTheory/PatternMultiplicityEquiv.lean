import Math.RepresentationTheory.PatternExteriorSource

/-! Order redundancy can be removed from the actual statistical source. -/
namespace Math.PatternMultiplicityEquiv
set_option autoImplicit false
noncomputable section
open Representation PatternExteriorSource
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) {n : ℕ} (p q : Fin n → S)

theorem source_le (e : Equiv.Perm (Fin n)) (he : p ∘ e = q) : Source r p ≤ Source r q := by
  change LinearMap.range (PatternExteriorSource.map r p).toLinearMap ≤ Source r q
  rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  simp only [PatternExteriorSource.map, PiTensorProduct.lift.tprod]
  change exteriorPower.ιMulti ℂ n (fun i => Pi.single (p i) (v i)) ∈ Source r q
  let w : Fin n → ∀ s, V s := fun i => Pi.single (p i) (v i)
  have hw : w ∘ e = fun i => Pi.single (q i) (w (e i) (q i)) := by
    funext i
    have hi := congrFun he i
    dsimp only [Function.comp_apply] at hi
    dsimp only [w, Function.comp_apply]
    rw [← hi, Pi.single_eq_same]
  have hp : exteriorPower.ιMulti ℂ n (w ∘ e) ∈ Source r q := by
    rw [hw]
    simpa only [pure_val] using (pure r q (fun i => w (e i) (q i))).property
  have hh := (exteriorPower.ιMulti ℂ n).map_congr_perm w e
  change exteriorPower.ιMulti ℂ n w ∈ Source r q
  rw [hh]
  simpa only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ] using
    (Source r q).smul_mem (((Equiv.Perm.sign e : ℤ) : ℂ)) hp

theorem source_eq (h : ∀ s, (Finset.univ.filter (fun i => p i = s)).card =
    (Finset.univ.filter (fun i => q i = s)).card) : Source r p = Source r q := by
  obtain ⟨e,he⟩ := (orbit_iff_counts q p).mpr h
  obtain ⟨f,hf⟩ := (orbit_iff_counts p q).mpr (fun s => (h s).symm)
  exact le_antisymm (source_le r p q e he) (source_le r q p f hf)

def equiv (h : ∀ s, (Finset.univ.filter (fun i => p i = s)).card =
    (Finset.univ.filter (fun i => q i = s)).card) :
    Representation.Equiv (representation r p) (representation r q) where
  toLinearEquiv :=
    { toFun := fun x => ⟨x.val, (source_eq r p q h).le x.property⟩
      invFun := fun x => ⟨x.val, (source_eq r p q h).ge x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

end
end Math.PatternMultiplicityEquiv
