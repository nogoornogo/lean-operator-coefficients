import Math.RepresentationTheory.Content.PatternMultiplicityEquiv

/-! Occupation sources exhaust the actual exterior representation. The
proof uses symbolic multilinearity, without constructing a concrete basis
or evaluating the finite family of words. All retained actions and arbitrary
equivariant targets are preserved. This is not irreducible branching. -/
namespace Math.FiniteExteriorExhaustion
set_option autoImplicit false
noncomputable section
open Representation PatternExteriorSource

variable {S G Y : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [AddCommGroup Y] [Module ℂ Y]
  (r : ∀ s, Representation ℂ G (V s)) (n : ℕ)

theorem sources_span : (⨆ p : Fin n → S, Source r p) = ⊤ := by
  apply top_unique
  rw [← exteriorPower.ιMulti_span ℂ n (∀ s, V s)]
  apply Submodule.span_le.mpr
  rintro _ ⟨v,rfl⟩
  have expand : exteriorPower.ιMulti ℂ n v =
      ∑ p : Fin n → S, (pure r p (fun i => v i (p i))).val := by
    calc
      _ = exteriorPower.ιMulti ℂ n (fun i => ∑ s, Pi.single s (v i s)) := by
        simp only [LinearMap.sum_single_apply]
      _ = _ := by
        simp only [pure_val]
        exact (exteriorPower.ιMulti ℂ n).toMultilinearMap.map_sum _
  rw [expand]
  apply Submodule.sum_mem
  intro p _
  exact (le_iSup (fun q : Fin n → S => Source r q) p) (pure r p _).property

/-- Bounded counts are data, not an enumeration of the words realizing them. -/
def counts (p : Fin n → S) (s : S) : Fin (n+1) :=
  ⟨(Finset.univ.filter (fun i => p i=s)).card,by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => p i=s)
    simpa using Nat.lt_succ_of_le h⟩

abbrev Occupation := Set.range (counts (S := S) n)

instance occupationFinite : Finite (Occupation (S := S) n) := inferInstance

def representative (c : Occupation (S := S) n) : Fin n → S := c.property.choose

omit [Fintype S] in
theorem representative_counts (c : Occupation (S := S) n) :
    counts n (representative n c)=c.val := c.property.choose_spec

theorem occupation_sum (c : Occupation (S := S) n) : ∑ s, (c.val s).val=n := by
  calc
    _ = ∑ s, (Finset.univ.filter (fun i => representative n c i=s)).card := by
      apply Finset.sum_congr rfl
      intro s _
      exact (congrArg Fin.val (congrFun (representative_counts n c) s)).symm
    _ = n := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ (representative n c)

def occupation (p : Fin n → S) : Occupation (S := S) n := ⟨counts n p,p,rfl⟩

theorem representative_source (p : Fin n → S) :
    Source r (representative n (occupation n p))=Source r p := by
  apply PatternMultiplicityEquiv.source_eq
  intro s
  exact congrArg Fin.val (congrFun (representative_counts n (occupation n p)) s)

/-- One source per realizable bounded count vector already exhausts the
exterior representation. No permutation list is constructed or evaluated. -/
theorem occupations_span :
    (⨆ c : Occupation (S := S) n, Source r (representative n c))=⊤ := by
  apply top_unique
  rw [← sources_span r n]
  apply iSup_le
  intro p
  rw [← representative_source r n p]
  exact le_iSup (fun c : Occupation (S := S) n => Source r (representative n c)) (occupation n p)

variable (target : Representation ℂ G Y)

def restrict (p : Fin n → S) (f : IntertwiningMap (Full r (n := n)) target) :
    IntertwiningMap (representation r p) target := f.comp (inclusion r p)

def extend (p : Fin n → S) (f : IntertwiningMap (representation r p) target) :
    IntertwiningMap (Full r (n := n)) target := f.comp (projection r p)

theorem restrict_extend (p : Fin n → S)
    (f : IntertwiningMap (representation r p) target) :
    restrict r n target p (extend r n target p f) = f := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f (projectionLinear r p x.val) = f x
  rw [projection_inclusion]

theorem restriction_ext (f g : IntertwiningMap (Full r (n := n)) target)
    (h : ∀ p, restrict r n target p f = restrict r n target p g) : f=g := by
  have hk : (⨆ p : Fin n → S, Source r p) ≤ LinearMap.ker (f.toLinearMap-g.toLinearMap) := by
    apply iSup_le
    intro p x hx
    change f x-g x=0
    exact sub_eq_zero.mpr (DFunLike.congr_fun (h p) ⟨x,hx⟩)
  rw [sources_span] at hk
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := hk (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ _))
  exact sub_eq_zero.mp hx

theorem occupation_ext (f g : IntertwiningMap (Full r (n := n)) target)
    (h : ∀ c : Occupation (S := S) n,
      restrict r n target (representative n c) f =
        restrict r n target (representative n c) g) : f=g := by
  have hk : (⨆ c : Occupation (S := S) n, Source r (representative n c)) ≤
      LinearMap.ker (f.toLinearMap-g.toLinearMap) := by
    apply iSup_le
    intro c x hx
    change f x-g x=0
    exact sub_eq_zero.mpr (DFunLike.congr_fun (h c) ⟨x,hx⟩)
  rw [occupations_span] at hk
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact sub_eq_zero.mp (hk (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ _)))

theorem nonzero_iff (f : IntertwiningMap (Full r (n := n)) target) :
    f≠0 ↔ ∃ p, restrict r n target p f≠0 := by
  constructor
  · intro hf
    by_contra hn
    push Not at hn
    apply hf
    apply restriction_ext r n target
    intro p
    rw [hn p]
    rfl
  · rintro ⟨p,hp⟩ hf
    apply hp
    subst f
    rfl

theorem exists_nonzero_iff :
    (∃ f : IntertwiningMap (Full r (n := n)) target, f≠0) ↔
      ∃ p : Fin n → S, ∃ f : IntertwiningMap (representation r p) target, f≠0 := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨p,hp⟩ := (nonzero_iff r n target f).mp hf
    exact ⟨p,restrict r n target p f,hp⟩
  · rintro ⟨p,f,hf⟩
    refine ⟨extend r n target p f,?_⟩
    intro he
    apply hf
    rw [← restrict_extend r n target p f,he]
    rfl

theorem nonzero_occupation_iff (f : IntertwiningMap (Full r (n := n)) target) :
    f≠0 ↔ ∃ c : Occupation (S := S) n,
      restrict r n target (representative n c) f≠0 := by
  constructor
  · intro hf
    by_contra hn
    push Not at hn
    apply hf
    apply occupation_ext r n target
    intro c
    rw [hn c]
    rfl
  · rintro ⟨c,hc⟩ hf
    apply hc
    subst f
    rfl

theorem exists_nonzero_occupation_iff :
    (∃ f : IntertwiningMap (Full r (n := n)) target, f≠0) ↔
      ∃ c : Occupation (S := S) n,
        ∃ f : IntertwiningMap (representation r (representative n c)) target, f≠0 := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨c,hc⟩ := (nonzero_occupation_iff r n target f).mp hf
    exact ⟨c,restrict r n target (representative n c) f,hc⟩
  · rintro ⟨c,f,hf⟩
    refine ⟨extend r n target (representative n c) f,?_⟩
    intro he
    apply hf
    rw [← restrict_extend r n target (representative n c) f,he]
    rfl

end
end Math.FiniteExteriorExhaustion
