import Math.RepresentationTheory.SU2.SU2PairDecomposition
import Math.RepresentationTheory.Exterior.GenerationExteriorExhaustion
import Math.RepresentationTheory.Exterior.IndexedExteriorContent

/-! Positive joint occurrence in three generations of a doublet-pair core.
The final condition uses only bounded exterior degrees and SU2 triangle/
parity paths. No character coefficient or equivariant Hom remains in it. -/
namespace Math.SU2PairGenerationSupport
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars SU2PairExterior SU2PairDecomposition
open scoped TensorProduct

@[reducible] local instance (a b : ℕ) : AddCommGroup (PairCarrier a b) := inferInstance
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Doublet ⊗[ℂ] Doublet) ⊗[ℂ] (Fin 3 → ℂ)) := inferInstance

abbrev generations := GenerationExteriorExhaustion.generations SU2PairExterior.tensor
abbrev Occupation (n : ℕ) := FiniteExteriorExhaustion.Occupation (S := Fin 3) n

def leaves (n : ℕ) (c : Occupation n) (i : Fin 3) : ExteriorContentTree.Leaf (Group × Group) where
  Carrier := Doublet ⊗[ℂ] Doublet
  rho := SU2PairExterior.tensor
  degree := (c.val i).val

def occupationEquiv (n : ℕ) (c : Occupation n) : Representation.Equiv
    ((SU2PairExterior.tensor.exteriorPower (c.val 0).val).tprod
      ((SU2PairExterior.tensor.exteriorPower (c.val 1).val).tprod
        (SU2PairExterior.tensor.exteriorPower (c.val 2).val)))
    (PatternExteriorSource.representation (GenerationExteriorExhaustion.fields SU2PairExterior.tensor)
      (FiniteExteriorExhaustion.representative n c)) :=
  IndexedExteriorContent.wordDecomposition 2 (leaves n c)
    (FiniteExteriorExhaustion.representative n c) (fun i =>
      congrArg Fin.val (congrFun (FiniteExteriorExhaustion.representative_counts n c) i))

def TripleSupport (n m l u v : ℕ) : Prop :=
  ∃ a b c d, CoreSupport n a b ∧
    (∃ e f g h, CoreSupport m e f ∧ CoreSupport l g h ∧
      SU2PairCoupling.Triangle e g c ∧ SU2PairCoupling.Triangle f h d) ∧
    SU2PairCoupling.Triangle a c u ∧ SU2PairCoupling.Triangle b d v

theorem occupation_target_iff (n u v : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (generations.exteriorPower n) (pair u v)) ↔
      ∃ c : Occupation n, TripleSupport (c.val 0).val (c.val 1).val (c.val 2).val u v := by
  rw [SelectionCriteria.Allowed,GenerationExteriorExhaustion.exists_nonzero_occupation_iff]
  apply exists_congr
  intro c
  constructor
  · rintro ⟨f,hf⟩
    apply (exterior_triple_target_iff (c.val 0).val (c.val 1).val (c.val 2).val u v).mp
    refine ⟨f.comp (occupationEquiv n c).toIntertwiningMap,?_⟩
    intro hz
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := (occupationEquiv n c).surjective x
    exact DFunLike.congr_fun hz y
  · intro h
    obtain ⟨f,hf⟩ :=
      (exterior_triple_target_iff (c.val 0).val (c.val 1).val (c.val 2).val u v).mpr h
    refine ⟨f.comp (occupationEquiv n c).symm.toIntertwiningMap,?_⟩
    intro hz
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := (occupationEquiv n c).symm.surjective x
    exact DFunLike.congr_fun hz y

theorem triple_capacity {n m l u v : ℕ} (h : TripleSupport n m l u v) :
    n≤4 ∧ m≤4 ∧ l≤4 := by
  rcases h with ⟨a,b,c,d,hn,⟨e,f,g,h,hm,hl,_⟩,_⟩
  unfold CoreSupport at hn hm hl
  omega

def tripleLeaves (n m l : ℕ) (i : Fin 3) : ExteriorContentTree.Leaf (Group × Group) where
  Carrier := Doublet ⊗[ℂ] Doublet
  rho := SU2PairExterior.tensor
  degree := (![n,m,l] : Fin 3 → ℕ) i

/-- Realize arbitrary three-count data without a word search. The existing
canonical content-tree word proves realizability symbolically. -/
theorem realize_counts (n m l : ℕ) :
    ∃ c : Occupation (n+(m+l)), (c.val 0).val=n ∧ (c.val 1).val=m ∧ (c.val 2).val=l := by
  let a := tripleLeaves n m l
  let p : Fin (n+(m+l)) → Fin 3 := IndexedExteriorContent.pattern 2 a
  let c := FiniteExteriorExhaustion.occupation (n+(m+l)) p
  refine ⟨c,?_,?_,?_⟩
  · exact IndexedExteriorContent.pattern_counts 2 a 0
  · exact IndexedExteriorContent.pattern_counts 2 a 1
  · exact IndexedExteriorContent.pattern_counts 2 a 2

/-- Complete bounded arithmetic support predicate for three generations,
including all nonsinglet weak/spin targets. -/
theorem target_iff (n u v : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (generations.exteriorPower n) (pair u v)) ↔
      ∃ a b c, a≤4 ∧ b≤4 ∧ c≤4 ∧ a+(b+c)=n ∧ TripleSupport a b c u v := by
  rw [occupation_target_iff]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨ha,hb,hd⟩ := triple_capacity hc
    refine ⟨_,_,_,ha,hb,hd,?_,hc⟩
    simpa [Fin.sum_univ_succ,add_assoc] using FiniteExteriorExhaustion.occupation_sum n c
  · rintro ⟨a,b,c,_,_,_,hs,h⟩
    subst n
    obtain ⟨c,hc₀,hc₁,hc₂⟩ := realize_counts a b c
    refine ⟨c,?_⟩
    rwa [hc₀,hc₁,hc₂]

end
end Math.SU2PairGenerationSupport
