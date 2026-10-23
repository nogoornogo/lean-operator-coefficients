import Math.RepresentationTheory.Protection.ProhibitionPatterns
import Mathlib.Data.Finset.Filter

/-! Necessary constraints pulled back to parameters; no model existence is inferred. -/
namespace Math.ProtectionConstraintPullback
set_option autoImplicit false
open Representation SelectionCriteria

/-- Keep inputs outside the certified applicability domain, rather than rejecting them. -/
def retain {X : Type*} (sm applicable necessary : X → Prop) (x : X) : Prop :=
  sm x ∧ (applicable x → necessary x)

theorem preserve {X : Type*} (sm applicable prohibition necessary : X → Prop)
    (certificate : ∀ x, applicable x → prohibition x → necessary x)
    (x : X) (hs : sm x) (hp : prohibition x) : retain sm applicable necessary x :=
  ⟨hs, fun ha => certificate x ha hp⟩

theorem exclude {X : Type*} (applicable prohibition necessary : X → Prop)
    (certificate : ∀ x, applicable x → prohibition x → necessary x)
    (x : X) (ha : applicable x) (hn : ¬ necessary x) : ¬ prohibition x :=
  fun hp => hn (certificate x ha hp)

theorem keep_outside {X : Type*} (sm applicable necessary : X → Prop)
    (x : X) (hs : sm x) (ha : ¬ applicable x) : retain sm applicable necessary x :=
  ⟨hs, fun h => False.elim (ha h)⟩

/-- Enumeration needs decidable predicates separately from its soundness certificate. -/
def finiteCandidates {X : Type*} [Fintype X]
    (sm applicable necessary : X → Prop) [DecidablePred (retain sm applicable necessary)] : Finset X :=
  Finset.univ.filter (retain sm applicable necessary)

theorem mem_finiteCandidates {X : Type*} [Fintype X]
    (sm applicable prohibition necessary : X → Prop)
    [DecidablePred (retain sm applicable necessary)]
    (certificate : ∀ x, applicable x → prohibition x → necessary x)
    (x : X) (hs : sm x) (hp : prohibition x) :
    x ∈ finiteCandidates sm applicable necessary := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, preserve sm applicable prohibition necessary certificate x hs hp⟩

section Cyclic
variable {X V : Type*} {k : ℕ} [NeZero k]
  [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  (r : X → Representation ℂ (CyclicCharge.Group k) V) (q : X → ZMod k)

def ScalarAdmission (x : X) : Prop :=
  ∀ g v, r x g v = MixedChargeSelection.cyclicCharacter g (q x) • v

theorem cyclic_necessary (x : X) (ha : ScalarAdmission r q x)
    (hp : Forbidden (IntertwiningMap (r x) (trivial ℂ (CyclicCharge.Group k) ℂ))) :
    q x ≠ 0 := (ProhibitionPatterns.cyclic_forbidden_iff (r x) (q x) ha).mp hp

theorem cyclic_retain (sm : X → Prop) (x : X) (hs : sm x)
    (hp : Forbidden (IntertwiningMap (r x) (trivial ℂ (CyclicCharge.Group k) ℂ))) :
    retain sm (ScalarAdmission r q) (fun x => q x ≠ 0) x :=
  ⟨hs, fun ha => cyclic_necessary r q x ha hp⟩

/-- Neutrality excludes protection only inside the nontrivial scalar-admitted domain. -/
theorem neutral_excludes (x : X) (ha : ScalarAdmission r q x) (hq : q x = 0) :
    ¬ Forbidden (IntertwiningMap (r x) (trivial ℂ (CyclicCharge.Group k) ℂ)) :=
  fun hp => cyclic_necessary r q x ha hp hq
end Cyclic
/-- Genuine cyclic lines provide a neutral-domain regression. -/
theorem neutral_line_not_forbidden :
    ¬ Forbidden (IntertwiningMap (CyclicCharge.representation (0 : ZMod 5))
      (trivial ℂ (CyclicCharge.Group 5) ℂ)) := by
  apply neutral_excludes (fun q : ZMod 5 => CyclicCharge.representation q) id 0
  · intro g v; rfl
  · rfl

/-- The zero-carrier exception is retained explicitly. -/
theorem zero_domain_control {H V : Type*} [Group H] [AddCommGroup V]
    [Module ℂ V] [Subsingleton V] :
    Forbidden (IntertwiningMap (trivial ℂ H V) (trivial ℂ H ℂ)) ∧
      ¬ ∃ _g : H, (1 : ℂ) ≠ 1 :=
  ScalarProhibitionNecessity.neutral_zero_control

end Math.ProtectionConstraintPullback
