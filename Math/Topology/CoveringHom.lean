import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Group.Basic

/-! Identity-based lifts of homomorphisms through covering homomorphisms.
The simply-connectedness hypothesis is explicit, not supplied by this module. -/

set_option autoImplicit false

namespace Math.CoveringHom

variable {H E B : Type*} [Group H] [Group E] [Group B]
  [TopologicalSpace H] [TopologicalSpace E] [TopologicalSpace B]
  [IsTopologicalGroup H] [IsTopologicalGroup E]

theorem existsUnique_lift [SimplyConnectedSpace H] [LocallyPathConnectedSpace H]
    (p : E →* B) (hp : IsCoveringMap p) (f : H →* B) (hf : Continuous f) :
    ∃! g : H →* E, Continuous g ∧ p.comp g = f := by
  obtain ⟨F, ⟨hF1, hFp⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨f, hf⟩ (1 : H) (1 : E) (by simp)
  have hproj (x : H) : p (F x) = f x := congrFun hFp x
  have hmul (x y : H) : F (x * y) = F x * F y := by
    have he := hp.eq_of_comp_eq
      (g₁ := fun z : H × H => F (z.1 * z.2))
      (g₂ := fun z : H × H => F z.1 * F z.2)
      (F.continuous.comp continuous_mul)
      ((F.continuous.comp continuous_fst).mul (F.continuous.comp continuous_snd))
      (by funext z; simp only [Function.comp_apply, map_mul, hproj])
      (1, 1) (by simp [hF1])
    exact congrFun he (x, y)
  let g : H →* E := { toFun := F, map_one' := hF1, map_mul' := hmul }
  refine ⟨g, ⟨F.continuous, ?_⟩, ?_⟩
  · ext x
    exact hproj x
  · intro g' hg'
    apply MonoidHom.ext
    have he := hp.eq_of_comp_eq hg'.1 F.continuous
      (by funext x; exact (congrArg (fun k : H →* B => k x) hg'.2).trans (hproj x).symm)
      1 (by simpa using hF1.symm)
    exact congrFun he

omit [TopologicalSpace H] [TopologicalSpace E] [TopologicalSpace B]
  [IsTopologicalGroup H] [IsTopologicalGroup E] in
theorem injective_of_comp {p : E →* B} {g : H →* E} {f : H →* B}
    (h : p.comp g = f) (hf : Function.Injective f) : Function.Injective g := by
  intro x y hxy
  apply hf
  rw [← h]
  exact congrArg p hxy

end Math.CoveringHom
