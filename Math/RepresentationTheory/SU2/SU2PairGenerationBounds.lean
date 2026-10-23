import Math.RepresentationTheory.SU2.SU2PairGenerationSupport

/-! Closed joint support for three generations of a doublet-pair core.
Sufficiency constructs positive coupling paths at the lower exterior degrees;
upper degrees use complementary core occupations. No multiplicity or rank
value is computed, and no character extraction premise is used. -/
namespace Math.SU2PairGenerationBounds
set_option autoImplicit false
noncomputable section
open SU2PairDecomposition SU2PairGenerationSupport SU2PairCoupling
open scoped TensorProduct

@[reducible] local instance (a b : ℕ) : AddCommGroup (SU2PairExterior.PairCarrier a b) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] (Fin 3 → ℂ)) := inferInstance

def Bounds (n u v : ℕ) : Prop :=
  n≤12 ∧ u≤n ∧ v≤n ∧ u≤12-n ∧ v≤12-n ∧ u+v≤6 ∧ u%2=n%2 ∧ v%2=n%2

theorem core_bounds {n a b : ℕ} (h : CoreSupport n a b) :
    n≤4 ∧ a≤n ∧ b≤n ∧ a≤4-n ∧ b≤4-n ∧ a+b≤2 ∧ a%2=n%2 ∧ b%2=n%2 := by
  unfold CoreSupport at h
  omega

theorem triple_bounds {n m l u v : ℕ} (h : TripleSupport n m l u v) : Bounds (n+(m+l)) u v := by
  rcases h with ⟨a,b,c,d,hn,⟨e,f,g,h,hm,hl,ht₁,ht₂⟩,ht₃,ht₄⟩
  obtain ⟨hn₀,ha,hb,ha',hb',hab,ha₂,hb₂⟩ := core_bounds hn
  obtain ⟨hm₀,he,hf,he',hf',hef,he₂,hf₂⟩ := core_bounds hm
  obtain ⟨hl₀,hg,hh,hg',hh',hgh,hg₂,hh₂⟩ := core_bounds hl
  have add_mod_eq {a b c d : ℕ} (ha : a%2=b%2) (hb : c%2=d%2) :
      (a+c)%2=(b+d)%2 := by
    calc
      _ = (a%2+c%2)%2 := Nat.add_mod _ _ _
      _ = (b%2+d%2)%2 := by rw [ha,hb]
      _ = _ := (Nat.add_mod _ _ _).symm
  have triangle_mod {a b c : ℕ} (h : Triangle a b c) : c%2=(a+b)%2 := by
    unfold Triangle at h
    omega
  have hc₂ := (triangle_mod ht₁).trans (add_mod_eq he₂ hg₂)
  have hd₂ := (triangle_mod ht₂).trans (add_mod_eq hf₂ hh₂)
  have hu₂ := (triangle_mod ht₃).trans (add_mod_eq ha₂ hc₂)
  have hv₂ := (triangle_mod ht₄).trans (add_mod_eq hb₂ hd₂)
  have hc := ht₁.1
  have hd := ht₂.1
  have hu := ht₃.1
  have hv := ht₄.1
  refine ⟨?_,?_,?_,?_,?_,?_,hu₂,hv₂⟩
  all_goals
    clear ha₂ hb₂ he₂ hf₂ hg₂ hh₂ hc₂ hd₂ hu₂ hv₂
    omega

theorem core_complement {n a b : ℕ} (hn : n≤4) :
    CoreSupport n a b ↔ CoreSupport (4-n) a b := by
  unfold CoreSupport
  omega

theorem triple_complement {n m l u v : ℕ} (h : TripleSupport n m l u v) :
    TripleSupport (4-n) (4-m) (4-l) u v := by
  obtain ⟨hn,hm,hl⟩ := triple_capacity h
  rcases h with ⟨a,b,c,d,h₁,⟨e,f,g,h,h₂,h₃,t₁,t₂⟩,t₃,t₄⟩
  exact ⟨a,b,c,d,(core_complement hn).mp h₁,
    ⟨e,f,g,h,(core_complement hm).mp h₂,(core_complement hl).mp h₃,t₁,t₂⟩,t₃,t₄⟩

theorem bounds_complement {n u v : ℕ} (h : Bounds n u v) : Bounds (12-n) u v := by
  unfold Bounds at *
  omega

/-- Explicit lower-half occupation and triangle paths. These are algebraic
constituent witnesses, not evaluations of numerical multiplicities. -/
theorem lower_paths {n u v : ℕ} (hn : n≤6) (h : Bounds n u v) :
    ∃ a b c, a≤4 ∧ b≤4 ∧ c≤4 ∧ a+(b+c)=n ∧ TripleSupport a b c u v := by
  unfold Bounds at h
  interval_cases n
  · refine ⟨0,0,0,by omega,by omega,by omega,rfl,?_⟩
    refine ⟨0,0,0,0,?_,⟨0,0,0,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
      simp [CoreSupport,Triangle] <;> omega
  · refine ⟨1,0,0,by omega,by omega,by omega,rfl,?_⟩
    refine ⟨1,1,0,0,?_,⟨0,0,0,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
      simp [CoreSupport,Triangle] <;> omega
  · refine ⟨1,1,0,by omega,by omega,by omega,rfl,?_⟩
    refine ⟨1,1,1,1,?_,⟨1,1,0,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
      simp [CoreSupport,Triangle] <;> omega
  · refine ⟨1,1,1,by omega,by omega,by omega,rfl,?_⟩
    refine ⟨1,1,2,2,?_,⟨1,1,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
      simp [CoreSupport,Triangle] <;> omega
  · refine ⟨2,1,1,by omega,by omega,by omega,rfl,?_⟩
    by_cases hu : u≤2
    · refine ⟨0,2,u,2,?_,⟨1,1,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
        simp [CoreSupport,Triangle] <;> omega
    · refine ⟨2,0,2,v,?_,⟨1,1,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
        simp [CoreSupport,Triangle] <;> omega
  · refine ⟨2,2,1,by omega,by omega,by omega,rfl,?_⟩
    by_cases hv : v=1
    · refine ⟨2,0,3,1,?_,⟨2,0,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
        simp [CoreSupport,Triangle] <;> omega
    · by_cases hu : u=1
      · refine ⟨0,2,1,3,?_,⟨0,2,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
          simp [CoreSupport,Triangle] <;> omega
      · refine ⟨2,0,1,3,?_,⟨0,2,1,1,?_,?_,?_,?_⟩,?_,?_⟩ <;>
          simp [CoreSupport,Triangle] <;> omega
  · refine ⟨2,2,2,by omega,by omega,by omega,rfl,?_⟩
    by_cases hv : v=0
    · by_cases hu : u≤4
      · refine ⟨2,0,2,0,?_,⟨2,0,2,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
          simp [CoreSupport,Triangle] <;> omega
      · refine ⟨2,0,4,0,?_,⟨2,0,2,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
          simp [CoreSupport,Triangle] <;> omega
    · by_cases hu : u=0
      · by_cases hv' : v≤4
        · refine ⟨0,2,0,2,?_,⟨0,2,0,2,?_,?_,?_,?_⟩,?_,?_⟩ <;>
            simp [CoreSupport,Triangle] <;> omega
        · refine ⟨0,2,0,4,?_,⟨0,2,0,2,?_,?_,?_,?_⟩,?_,?_⟩ <;>
            simp [CoreSupport,Triangle] <;> omega
      · by_cases hv' : v=2
        · refine ⟨2,0,2,2,?_,⟨2,0,0,2,?_,?_,?_,?_⟩,?_,?_⟩ <;>
            simp [CoreSupport,Triangle] <;> omega
        · refine ⟨0,2,2,2,?_,⟨0,2,2,0,?_,?_,?_,?_⟩,?_,?_⟩ <;>
            simp [CoreSupport,Triangle] <;> omega

theorem paths_iff (n u v : ℕ) :
    (∃ a b c, a≤4 ∧ b≤4 ∧ c≤4 ∧ a+(b+c)=n ∧ TripleSupport a b c u v) ↔ Bounds n u v := by
  constructor
  · rintro ⟨a,b,c,_,_,_,rfl,h⟩
    exact triple_bounds h
  · intro h
    by_cases hn : n≤6
    · exact lower_paths hn h
    · have hc := bounds_complement h
      obtain ⟨a,b,c,ha,hb,hc',hs,hp⟩ := lower_paths (by unfold Bounds at h; omega) hc
      refine ⟨4-a,4-b,4-c,by omega,by omega,by omega,?_,triple_complement hp⟩
      unfold Bounds at h
      omega

theorem target_iff (n u v : ℕ) :
    Math.SelectionCriteria.Allowed (Representation.IntertwiningMap
      (SU2PairGenerationSupport.generations.exteriorPower n) (SU2PairExterior.pair u v)) ↔ Bounds n u v :=
  (SU2PairGenerationSupport.target_iff n u v).trans (paths_iff n u v)

end
end Math.SU2PairGenerationBounds
