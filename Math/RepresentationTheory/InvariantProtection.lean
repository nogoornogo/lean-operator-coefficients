import Math.RepresentationTheory.InvariantHomRestriction
import Mathlib.LinearAlgebra.DFinsupp

/-! Symmetry enhancement is a statement about every admitted coefficient,
not the existence of one invariant or the vanishing of an arbitrary selector. -/
namespace Math.InvariantProtection
set_option autoImplicit false
noncomputable section
open Representation
variable {k H K V : Type*} [Field k] [Group H] [Group K]
  [AddCommGroup V] [Module k V]
  (a : Representation k H V) (j : K →* H)

/-- Every coefficient invariant under the supplied smaller action respects
all of the larger action. No surjectivity of the group map is assumed. -/
def Protected : Prop := ∀ f : InvariantHomRestriction.Space (a.comp j),
  ∀ h v, f (a h v) = f v

theorem protected_iff_surjective : Protected a j ↔
    Function.Surjective (InvariantHomRestriction.restrict a j) := by
  constructor
  · intro hp f
    let q : InvariantHomRestriction.Space a := {
      toLinearMap := f.toLinearMap
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        exact hp f h v }
    exact ⟨q, IntertwiningMap.ext rfl⟩
  · intro hs f h v
    obtain ⟨q, rfl⟩ := hs f
    exact IntertwiningMap.isIntertwining _ _ q h v

/-- A prescribed flavor selector is a separate linear map; protection of it
means its whole restriction vanishes, not merely one coefficient. -/
theorem selector_zero_iff {W : Type*} [AddCommGroup W] [Module k W]
    (s : InvariantHomRestriction.Space (a.comp j) →ₗ[k] W) :
    (∀ f, s f = 0) ↔ s = 0 := by
  constructor
  · intro h; exact LinearMap.ext h
  · rintro rfl f; rfl

section Families
variable {I : Type*} {A B : I → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
  (r : ∀ i, A i →ₗ[k] B i)

def familyMap : (∀ i, A i) →ₗ[k] (∀ i, B i) :=
  LinearMap.pi fun i => (r i).comp (LinearMap.proj i)

theorem family_surjective_iff : Function.Surjective (familyMap r) ↔
    ∀ i, Function.Surjective (r i) := by
  classical
  constructor
  · intro hs i b
    obtain ⟨f, hf⟩ := hs (Pi.single i b)
    exact ⟨f i, by simpa [familyMap] using congrFun hf i⟩
  · intro hs b
    choose f hf using fun i => hs i (b i)
    exact ⟨f, funext hf⟩

theorem finite_support_surjective_iff :
    Function.Surjective (DFinsupp.mapRange.linearMap r) ↔
      Function.Surjective (familyMap r) :=
  (DFinsupp.mapRange_surjective (fun i => r i) (fun i => (r i).map_zero)).trans
    (family_surjective_iff r).symm

/-- Finitely supported interactions and the full coefficient product have
identical total-vanishing tests, but are different spaces. -/
theorem finite_support_forbidden_iff : (∀ f : Π₀ i, B i, f = 0) ↔
    ∀ i, ∀ b : B i, b = 0 := by
  classical
  constructor
  · intro h i b
    have he := congrArg (fun f : Π₀ i, B i => f i) (h (DFinsupp.single i b))
    simpa using he
  · intro h f
    ext i
    exact h i (f i)

theorem product_forbidden_iff : (∀ f : ∀ i, B i, f = 0) ↔
    ∀ i, ∀ b : B i, b = 0 := by
  classical
  constructor
  · intro h i b
    have he := congrFun (h (Pi.single i b)) i
    simpa using he
  · intro h f
    funext i
    exact h i (f i)
end Families

/-- A commuting extraction square transports surjectivity, without defining
restriction by conjugating the completeness equivalences. -/
theorem square_surjective_iff {A B X Y : Type*}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (e : A ≃ₗ[k] X) (f : B ≃ₗ[k] Y)
    (r : A →ₗ[k] B) (s : X →ₗ[k] Y)
    (h : ∀ x, f (r x) = s (e x)) :
    Function.Surjective r ↔ Function.Surjective s := by
  constructor
  · intro hr y
    obtain ⟨b, rfl⟩ := f.surjective y
    obtain ⟨a, rfl⟩ := hr b
    exact ⟨e a, (h a).symm⟩
  · intro hs b
    obtain ⟨x, hx⟩ := hs (f b)
    obtain ⟨a, rfl⟩ := e.surjective x
    exact ⟨a, f.injective ((h a).trans hx)⟩
end
end Math.InvariantProtection
