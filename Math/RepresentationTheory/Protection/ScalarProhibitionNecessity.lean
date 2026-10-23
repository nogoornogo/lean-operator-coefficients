import Math.RepresentationTheory.Protection.MixedScalarSelection
import Math.LinearAlgebra.Selection.SelectionCriteria
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Necessity of scalar detection requires a nonzero admitted carrier. -/
namespace Math.ScalarProhibitionNecessity
noncomputable section
open Representation SelectionCriteria
variable {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]

theorem forbidden_iff_detect [Nontrivial V] (r : Representation ℂ H V)
    (z : H → ℂ) (hs : ∀ g v, r g v = z g • v) :
    Forbidden (IntertwiningMap r (trivial ℂ H ℂ)) ↔ ∃ g, z g ≠ 1 := by
  classical
  constructor
  · intro h
    by_contra hn
    have hz : ∀ g, z g = 1 := by simpa using hn
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
    let q : IntertwiningMap r (trivial ℂ H ℂ) :=
      { toLinearMap := f
        isIntertwining' g := by
          apply LinearMap.ext
          intro w
          simp [hs, hz] }
    have he := congrArg (fun q : IntertwiningMap r (trivial ℂ H ℂ) => q v) (h q)
    exact hf he
  · rintro ⟨g, hg⟩ f
    exact MixedScalarSelection.invariant_zero r g (z g) hg (hs g) f

/-- Any map from a forbidden domain to an allowed domain fails surjectivity. -/
theorem not_surjective {C D : Type*} [Zero C] [Zero D]
    (f : C → D) (hf : f 0 = 0) (hc : Forbidden C) (hd : Allowed D) :
    ¬ Function.Surjective f := by
  rintro h
  obtain ⟨d, hd⟩ := hd
  obtain ⟨c, rfl⟩ := h d
  exact hd ((congrArg f (hc c)).trans hf)

/-- Neutrality on a zero carrier does not force a nonzero functional. -/
theorem zero_carrier_forbidden (r : Representation ℂ H V) [Subsingleton V] :
    Forbidden (IntertwiningMap r (trivial ℂ H ℂ)) := by
  intro f
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  rw [Subsingleton.elim v 0]
  exact map_zero f
/-- Explicit negative control for dropping Nontrivial from the detection converse. -/
theorem neutral_zero_control [Subsingleton V] :
    Forbidden (IntertwiningMap (trivial ℂ H V) (trivial ℂ H ℂ)) ∧
      ¬ ∃ _g : H, (1 : ℂ) ≠ 1 :=
  ⟨zero_carrier_forbidden _, by simp⟩
end
end Math.ScalarProhibitionNecessity
