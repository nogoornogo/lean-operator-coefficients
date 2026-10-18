import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Finsupp.Basic

/-!
# Character restriction obstructions

Conjugation in an ambient group forces invariance of restricted characters.
The same necessary condition holds for finite integer combinations of actual
finite-dimensional representations, over any field. A target violating it is
outside the restriction image.

The parameter space need not be a group, and its map into the ambient group
need not be injective. No continuity, compactness, semisimplicity, source
Laurent model, or character-classification theorem is used.

The evaluator lemmas are independent of representations: an injective,
action-compatible target evaluator transfers non-fixedness to functions.
-/

namespace Math.CharacterRestriction

section Functions

variable {T K I P : Type*}

/-- A non-invariant target is outside any family of invariant functions. -/
theorem not_mem_range_of_not_invariant
    (action : T → T) (source : I → T → K)
    (hsource : ∀ i t, source i (action t) = source i t)
    (target : T → K) (htarget : ¬ ∀ t, target (action t) = target t) :
    target ∉ Set.range source := by
  rintro ⟨i, rfl⟩
  exact htarget (hsource i)

/-- A single point witnessing non-invariance suffices. -/
theorem not_mem_range_of_ne
    (action : T → T) (source : I → T → K)
    (hsource : ∀ i t, source i (action t) = source i t)
    (target : T → K) (t : T) (htarget : target (action t) ≠ target t) :
    target ∉ Set.range source :=
  not_mem_range_of_not_invariant action source hsource target
    (fun h => htarget (h t))

/-- Faithful compatible evaluation reflects invariance of a target model. -/
theorem fixed_of_faithful_eval
    (eval : P → T → K) (hfaithful : Function.Injective eval)
    (modelAction : P → P) (action : T → T)
    (hcompatible : ∀ p t, eval (modelAction p) t = eval p (action t))
    (p : P) (hinvariant : ∀ t, eval p (action t) = eval p t) :
    modelAction p = p := by
  apply hfaithful
  funext t
  exact (hcompatible p t).trans (hinvariant t)

/-- Only the target needs a faithful model; source functions can be arbitrary. -/
theorem not_mem_range_of_nonfixed_model
    (eval : P → T → K) (hfaithful : Function.Injective eval)
    (modelAction : P → P) (action : T → T)
    (hcompatible : ∀ p t, eval (modelAction p) t = eval p (action t))
    (source : I → T → K)
    (hsource : ∀ i t, source i (action t) = source i t)
    (p : P) (hp : modelAction p ≠ p) :
    eval p ∉ Set.range source := by
  apply not_mem_range_of_not_invariant action source hsource (eval p)
  intro hinvariant
  exact hp (fixed_of_faithful_eval eval hfaithful modelAction action hcompatible p hinvariant)

end Functions

section Representations

variable {G T k : Type*} [Group G] [Field k]

/-- Pulling back a character along an action implemented by conjugation
produces an invariant function. -/
theorem character_restriction_invariant
    {V : Type*} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (incl : T → G) (action : T → T) (n : G)
    (hconj : ∀ t, incl (action t) = n * incl t * n⁻¹) (t : T) :
    rho.character (incl (action t)) = rho.character (incl t) := by
  rw [hconj t]
  exact rho.char_conj (incl t) n

variable {I : Type*} {V : I → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A finite integer combination of actual finite-dimensional characters.
This is a coefficient presentation, not a claimed Grothendieck-ring model. -/
noncomputable def virtualCharacter [∀ i, FiniteDimensional k (V i)]
    (rho : ∀ i, Representation k G (V i)) (coeff : I →₀ ℤ) (g : G) : k :=
  coeff.sum (fun i n => n • (rho i).character g)

variable [∀ i, FiniteDimensional k (V i)]

@[simp]
theorem virtualCharacter_zero
    (rho : ∀ i, Representation k G (V i)) (g : G) :
    virtualCharacter rho 0 g = 0 := by
  simp [virtualCharacter]

@[simp]
theorem virtualCharacter_add
    (rho : ∀ i, Representation k G (V i)) (a b : I →₀ ℤ) (g : G) :
    virtualCharacter rho (a + b) g = virtualCharacter rho a g + virtualCharacter rho b g := by
  classical
  exact Finsupp.sum_add_index' (by intro i; simp) (by intro i m n; exact add_zsmul _ _ _)

@[simp]
theorem virtualCharacter_single
    (rho : ∀ i, Representation k G (V i)) (i : I) (n : ℤ) (g : G) :
    virtualCharacter rho (Finsupp.single i n) g = n • (rho i).character g := by
  classical
  simp [virtualCharacter]

/-- Finite signed combinations obey the same restriction constraint. -/
theorem virtualCharacter_restriction_invariant
    (rho : ∀ i, Representation k G (V i)) (coeff : I →₀ ℤ)
    (incl : T → G) (action : T → T) (n : G)
    (hconj : ∀ t, incl (action t) = n * incl t * n⁻¹) (t : T) :
    virtualCharacter rho coeff (incl (action t)) = virtualCharacter rho coeff (incl t) := by
  classical
  unfold virtualCharacter Finsupp.sum
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x : k => coeff i • x)
    (character_restriction_invariant (rho i) incl action n hconj t)

/-- A non-invariant target cannot be the restriction of a finite virtual
character from any supplied family of finite-dimensional representations. -/
theorem not_mem_virtualRestrictionImage
    (rho : ∀ i, Representation k G (V i))
    (incl : T → G) (action : T → T) (n : G)
    (hconj : ∀ t, incl (action t) = n * incl t * n⁻¹)
    (target : T → k) (htarget : ¬ ∀ t, target (action t) = target t) :
    target ∉ Set.range (fun coeff : I →₀ ℤ => virtualCharacter rho coeff ∘ incl) :=
  not_mem_range_of_not_invariant action _
    (fun coeff t => virtualCharacter_restriction_invariant rho coeff incl action n hconj t)
    target htarget

/-- The faithful target-model version needs no polynomial realization of
the source representations. -/
theorem not_mem_virtualRestrictionImage_of_nonfixed_model
    {P : Type*} (rho : ∀ i, Representation k G (V i))
    (incl : T → G) (action : T → T) (n : G)
    (hconj : ∀ t, incl (action t) = n * incl t * n⁻¹)
    (eval : P → T → k) (hfaithful : Function.Injective eval)
    (modelAction : P → P)
    (hcompatible : ∀ p t, eval (modelAction p) t = eval p (action t))
    (p : P) (hp : modelAction p ≠ p) :
    eval p ∉ Set.range (fun coeff : I →₀ ℤ => virtualCharacter rho coeff ∘ incl) :=
  not_mem_range_of_nonfixed_model eval hfaithful modelAction action hcompatible _
    (fun coeff t => virtualCharacter_restriction_invariant rho coeff incl action n hconj t)
    p hp

end Representations

section AllRepresentations

variable {G T k : Type*} [Group G] [Field k]

/-- Restriction of finite integer combinations indexed by all bundled
finite-dimensional representations, not just a chosen list of generators. -/
noncomputable def virtualRestriction (incl : T → G) (coeff : FDRep k G →₀ ℤ) : T → k :=
  virtualCharacter (fun R : FDRep k G => R.ρ) coeff ∘ incl

/-- The target is outside the image of all finite virtual characters
presented using mathlib's actual `FDRep` objects. -/
theorem not_mem_finiteVirtualRestrictionImage
    (incl : T → G) (action : T → T) (n : G)
    (hconj : ∀ t, incl (action t) = n * incl t * n⁻¹)
    (target : T → k) (htarget : ¬ ∀ t, target (action t) = target t) :
    target ∉ Set.range (virtualRestriction incl) :=
  not_mem_virtualRestrictionImage (fun R : FDRep k G => R.ρ)
    incl action n hconj target htarget

end AllRepresentations

end Math.CharacterRestriction
