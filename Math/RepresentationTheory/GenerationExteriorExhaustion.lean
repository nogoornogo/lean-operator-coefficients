import Math.RepresentationTheory.FiniteExteriorExhaustion
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Complete occupation restriction for three independent generation
summands. Arbitrary retained group actions and equivariant targets are
preserved. This constructs no irreducible catalogue or numerical table. -/
namespace Math.GenerationExteriorExhaustion
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V Y : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup Y] [Module ℂ Y]
  (r : Representation ℂ G V)

abbrev fields (_ : Fin 3) := r
abbrev generations := r.tprod (Representation.trivial ℂ G (Fin 3 → ℂ))

/-- The finite tensor/product equivalence is equivariant for the full group,
not just for a chosen torus or one of the semisimple factors. -/
def equivalence : Representation.Equiv (generations r)
    (FiniteSpeciesExterior.representation (fields r)) where
  toLinearEquiv := TensorProduct.piScalarRight ℂ ℂ V (Fin 3)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x a
    funext i
    simp [TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul,
      Representation.tprod_apply,FiniteSpeciesExterior.representation_apply]

variable (n : ℕ) (target : Representation ℂ G Y)

abbrev split := (equivalence r).exteriorPower n

def restrict (p : Fin n → Fin 3)
    (f : IntertwiningMap ((generations r).exteriorPower n) target) :
    IntertwiningMap (PatternExteriorSource.representation (fields r) p) target :=
  FiniteExteriorExhaustion.restrict (fields r) n target p
    (f.comp (split r n).symm.toIntertwiningMap)

def extend (p : Fin n → Fin 3)
    (f : IntertwiningMap (PatternExteriorSource.representation (fields r) p) target) :
    IntertwiningMap ((generations r).exteriorPower n) target :=
  (FiniteExteriorExhaustion.extend (fields r) n target p f).comp
    (split r n).toIntertwiningMap

theorem restrict_extend (p : Fin n → Fin 3)
    (f : IntertwiningMap (PatternExteriorSource.representation (fields r) p) target) :
    restrict r n target p (extend r n target p f) = f := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f (PatternExteriorSource.projectionLinear (fields r) p
    ((split r n) ((split r n).symm x.val))) = f x
  rw [Representation.Equiv.apply_symm_apply,PatternExteriorSource.projection_inclusion]

theorem restriction_ext
    (f g : IntertwiningMap ((generations r).exteriorPower n) target)
    (h : ∀ p, restrict r n target p f = restrict r n target p g) : f=g := by
  have he := FiniteExteriorExhaustion.restriction_ext (fields r) n target
    (f.comp (split r n).symm.toIntertwiningMap)
    (g.comp (split r n).symm.toIntertwiningMap) h
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun he ((split r n) x)
  simpa using hx

theorem nonzero_iff (f : IntertwiningMap ((generations r).exteriorPower n) target) :
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
    (∃ f : IntertwiningMap ((generations r).exteriorPower n) target, f≠0) ↔
      ∃ p : Fin n → Fin 3,
        ∃ f : IntertwiningMap (PatternExteriorSource.representation (fields r) p) target, f≠0 := by
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

theorem occupation_ext
    (f g : IntertwiningMap ((generations r).exteriorPower n) target)
    (h : ∀ c : FiniteExteriorExhaustion.Occupation (S := Fin 3) n,
      restrict r n target (FiniteExteriorExhaustion.representative n c) f =
        restrict r n target (FiniteExteriorExhaustion.representative n c) g) : f=g := by
  have he := FiniteExteriorExhaustion.occupation_ext (fields r) n target
    (f.comp (split r n).symm.toIntertwiningMap)
    (g.comp (split r n).symm.toIntertwiningMap) h
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun he ((split r n) x)
  simpa using hx

/-- Only realizable count vectors, rather than all generation words, are
needed to detect a nonzero equivariant coefficient. This still leaves the
individual target occurrences to be proved. -/
theorem nonzero_occupation_iff (f : IntertwiningMap ((generations r).exteriorPower n) target) :
    f≠0 ↔ ∃ c : FiniteExteriorExhaustion.Occupation (S := Fin 3) n,
      restrict r n target (FiniteExteriorExhaustion.representative n c) f≠0 := by
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
    (∃ f : IntertwiningMap ((generations r).exteriorPower n) target, f≠0) ↔
      ∃ c : FiniteExteriorExhaustion.Occupation (S := Fin 3) n,
        ∃ f : IntertwiningMap
          (PatternExteriorSource.representation (fields r) (FiniteExteriorExhaustion.representative n c))
          target, f≠0 := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨c,hc⟩ := (nonzero_occupation_iff r n target f).mp hf
    exact ⟨c,restrict r n target (FiniteExteriorExhaustion.representative n c) f,hc⟩
  · rintro ⟨c,f,hf⟩
    refine ⟨extend r n target (FiniteExteriorExhaustion.representative n c) f,?_⟩
    intro he
    apply hf
    rw [← restrict_extend r n target (FiniteExteriorExhaustion.representative n c) f,he]
    rfl

end
end Math.GenerationExteriorExhaustion
