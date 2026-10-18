import Math.RepresentationTheory.ProhibitionPatterns
import Math.LinearAlgebra.MixedSelectionRequests

namespace GUT.SU6CyclicPatternSearch
set_option autoImplicit false
noncomputable section
open Math Representation Math.SelectionCriteria

def qque (x y h : ZMod 5) : ZMod 5 := 2*x-(-x-h)-(-y+h)
def llhh (y h : ZMod 5) : ZMod 5 := 2*(y+h)

theorem qque_simplify (x y h : ZMod 5) : qque x y h = 3*x+y := by
  unfold qque
  ring

theorem witness : qque 1 0 0 ≠ 0 ∧ llhh 0 0 = 0 := by decide

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Nontrivial W]

/-- The actual local/residual carrier and scalar-action certificates are inputs. -/
theorem mixed_iff (x y h : ZMod 5)
    (r : Representation ℂ (CyclicCharge.Group 5) V)
    (s : Representation ℂ (CyclicCharge.Group 5) W)
    (hr : ∀ g v, r g v = MixedChargeSelection.cyclicCharacter g (qque x y h) • v)
    (hs : ∀ g w, s g w = MixedChargeSelection.cyclicCharacter g (llhh y h) • w) :
    (Forbidden (IntertwiningMap r (trivial ℂ (CyclicCharge.Group 5) ℂ)) ∧
      Allowed (IntertwiningMap s (trivial ℂ (CyclicCharge.Group 5) ℂ))) ↔
      qque x y h ≠ 0 ∧ llhh y h = 0 := by
  have hf := Math.ProhibitionPatterns.cyclic_forbidden_iff r (qque x y h) hr
  have hg := Math.ProhibitionPatterns.cyclic_forbidden_iff s (llhh y h) hs
  rw [forbidden_iff_not_allowed] at hg
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨hf.mp h1, by by_contra hn; exact hg.mpr hn h2⟩
  · rintro ⟨h1,h2⟩
    refine ⟨hf.mpr h1, ?_⟩
    apply Math.ProhibitionPatterns.cyclic_neutral_allowed s
    simpa [h2] using hs

/-- In a common coefficient universe, packaging adds no new carrier premise. -/
theorem package (C : Bool → Type*) [∀ i, Zero (C i)]
    (hf : Forbidden (C false)) (ha : Allowed (C true)) :
    Math.MixedSelectionRequests.Satisfies C
      ⟨{false}, {true}⟩ := by
  constructor
  · intro i hi; simp only [Set.mem_singleton_iff] at hi; subst i; exact hf
  · intro i hi; simp only [Set.mem_singleton_iff] at hi; subst i; exact ha

/-- Executable pattern test on actual character lines, not physical operators. -/
theorem character_line_iff (x y h : ZMod 5) :
    (Forbidden (IntertwiningMap (CyclicCharge.representation (qque x y h))
        (trivial ℂ (CyclicCharge.Group 5) ℂ)) ∧
      Allowed (IntertwiningMap (CyclicCharge.representation (llhh y h))
        (trivial ℂ (CyclicCharge.Group 5) ℂ))) ↔
      qque x y h ≠ 0 ∧ llhh y h = 0 := by
  apply mixed_iff
  · intro g v; rfl
  · intro g v; rfl

theorem character_line_witness :
    Forbidden (IntertwiningMap (CyclicCharge.representation (qque 1 0 0))
        (trivial ℂ (CyclicCharge.Group 5) ℂ)) ∧
      Allowed (IntertwiningMap (CyclicCharge.representation (llhh 0 0))
        (trivial ℂ (CyclicCharge.Group 5) ℂ)) :=
  (character_line_iff 1 0 0).mpr witness

end
end GUT.SU6CyclicPatternSearch
