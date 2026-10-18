import Math.RepresentationTheory.PatternExteriorSource

/-! Bijections of species, with equivariant field identifications, transport
actual statistical images rather than ordered tensor surrogates. -/
namespace Math.PatternSpeciesEquiv
set_option autoImplicit false
noncomputable section
open Representation
variable {S T G : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] [Group G]
  {V : S → Type*} {W : T → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [∀ t, AddCommGroup (W t)] [∀ t, Module ℂ (W t)]
  (r : ∀ s, Representation ℂ G (V s)) (a : ∀ t, Representation ℂ G (W t))
  (e : S ≃ T) (h : ∀ s, Representation.Equiv (r s) (a (e s)))
  {n : ℕ} (p : Fin n → S)

def total : (∀ s, V s) ≃ₗ[ℂ] (∀ t, W t) :=
  (LinearEquiv.piCongrRight (fun s => (h s).toLinearEquiv)).trans (LinearEquiv.piCongrLeft ℂ W e)

omit [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] in
@[simp] theorem total_at (x : ∀ s, V s) (s : S) : total r a e h x (e s) = h s (x s) := by
  change (Equiv.piCongrLeft W e) (fun s => h s (x s)) (e s) = _
  exact Equiv.piCongrLeft_apply_apply W e _ s

omit [Fintype S] [Fintype T] in
theorem total_single (s : S) (x : V s) : total r a e h (Pi.single s x) = Pi.single (e s) (h s x) := by
  funext t
  obtain ⟨u,rfl⟩ := e.surjective t
  rw [total_at]
  by_cases hs : s = u
  · subst u; simp
  · simp [Pi.single_eq_of_ne (Ne.symm hs), Pi.single_eq_of_ne (Ne.symm (fun hu => hs (e.injective hu)))]

def raw : PatternExteriorSource.Source r p →ₗ[ℂ] ⋀[ℂ]^n (∀ t, W t) :=
  (exteriorPower.map n (total r a e h).toLinearMap).comp (PatternExteriorSource.Source r p).subtype

def forward : PatternExteriorSource.Source r p →ₗ[ℂ] PatternExteriorSource.Source a (e ∘ p) :=
  (PatternExteriorSource.projectionLinear a (e ∘ p)).comp (raw r a e h p)

theorem raw_pure (v : ∀ i, V (p i)) : raw r a e h p (PatternExteriorSource.pure r p v) =
    (PatternExteriorSource.pure a (e ∘ p) (fun i => h (p i) (v i))).val := by
  simp only [raw,LinearMap.comp_apply,Submodule.subtype_apply,PatternExteriorSource.pure_val,
    exteriorPower.map_apply_ιMulti]
  exact congrArg (exteriorPower.ιMulti ℂ n) (funext fun i => total_single r a e h (p i) (v i))

theorem forward_pure (v : ∀ i, V (p i)) : forward r a e h p (PatternExteriorSource.pure r p v) =
    PatternExteriorSource.pure a (e ∘ p) (fun i => h (p i) (v i)) := by
  rw [forward,LinearMap.comp_apply,raw_pure]
  exact PatternExteriorSource.projection_inclusion _ _ _

theorem source_ext {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {f g : PatternExteriorSource.Source r p →ₗ[ℂ] Y}
    (he : ∀ v, f (PatternExteriorSource.pure r p v) = g (PatternExteriorSource.pure r p v)) : f = g := by
  have hh : f.comp (PatternExteriorSource.onto r p).toLinearMap =
      g.comp (PatternExteriorSource.onto r p).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    exact he
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := PatternExteriorSource.onto_surjective r p x
  exact LinearMap.congr_fun hh y

theorem inclusion_forward : (PatternExteriorSource.Source a (e ∘ p)).subtype.comp
    (forward r a e h p) = raw r a e h p := by
  apply source_ext r p
  intro v
  change (forward r a e h p (PatternExteriorSource.pure r p v)).val = _
  rw [forward_pure,raw_pure]

theorem forward_injective : Function.Injective (forward r a e h p) := by
  intro x y he
  have hr : raw r a e h p x = raw r a e h p y :=
    (LinearMap.congr_fun (inclusion_forward r a e h p) x).symm.trans
      ((congrArg Subtype.val he).trans (LinearMap.congr_fun (inclusion_forward r a e h p) y))
  exact Subtype.ext (exteriorPower.map_injective_field (n := n) (total r a e h).injective hr)

theorem forward_surjective : Function.Surjective (forward r a e h p) := by
  have hh : LinearMap.range (PatternExteriorSource.onto a (e ∘ p)).toLinearMap ≤
      LinearMap.range (forward r a e h p) := by
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top,Submodule.map_span,Submodule.span_le]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    refine ⟨PatternExteriorSource.pure r p (fun i => (h (p i)).symm (v i)), ?_⟩
    rw [forward_pure]
    simp
    rfl
  have ht := LinearMap.range_eq_top.mpr (PatternExteriorSource.onto_surjective a (e ∘ p))
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (ht ▸ hh))

def equiv : Representation.Equiv (PatternExteriorSource.representation r p)
    (PatternExteriorSource.representation a (e ∘ p)) where
  toLinearEquiv := LinearEquiv.ofBijective (forward r a e h p)
    ⟨forward_injective r a e h p,forward_surjective r a e h p⟩
  isIntertwining' g := by
    apply source_ext r p
    intro v
    change forward r a e h p (PatternExteriorSource.representation r p g (PatternExteriorSource.pure r p v)) =
      PatternExteriorSource.representation a (e ∘ p) g (forward r a e h p (PatternExteriorSource.pure r p v))
    rw [← PatternExteriorSource.pure_action,forward_pure,forward_pure,← PatternExteriorSource.pure_action]
    apply congrArg (PatternExteriorSource.pure a (e ∘ p))
    funext i
    exact (h (p i)).isIntertwining _ _ g (v i)

end
end Math.PatternSpeciesEquiv
