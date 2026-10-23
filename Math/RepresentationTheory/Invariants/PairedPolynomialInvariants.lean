import Math.RepresentationTheory.Constructions.PolynomialRealForm
import Math.RepresentationTheory.Invariants.GeneratorInvariantTests

/-! Separating two polynomial group factors along a conjugate-diagonal action. -/
namespace Math.PairedPolynomialInvariants
set_option autoImplicit false
noncomputable section
open Representation MvPolynomial
variable {G V A : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ (G × G) V) (conjugate : G →* G)
  (family : A → ℂ → G)

def paired : G →* G × G := (MonoidHom.id G).prod conjugate

def PolynomialOrbits : Prop := ∀ a (f : Module.Dual ℂ V) x,
  ∃ p : MvPolynomial (Fin 2) ℂ, ∀ u v, eval ![u,v] p = f (rho (family a u,family a v) x)

theorem fixed_iff (hg : Subgroup.closure (Set.range (fun az : A × ℂ => family az.1 az.2)) = ⊤)
    (hc : ∀ a z, conjugate (family a z) = family a (star z))
    (hzero : ∀ a, family a 0 = 1) (hp : PolynomialOrbits rho family)
    (f : Module.Dual ℂ V) :
    (∀ g x, f (rho (paired conjugate g) x) = f x) ↔ ∀ g x, f (rho g x) = f x := by
  constructor
  · intro hf
    have ht (a : A) (u v : ℂ) (x : V) : f (rho (family a u,family a v) x) = f x := by
      obtain ⟨p,he⟩ := hp a f x
      have hz : p - C (f x) = 0 := PolynomialRealForm.zero_of_conjugate_diagonal _ (by
        intro z
        simp only [map_sub, eval_C, he]
        have h := hf (family a z) x
        simpa only [paired, MonoidHom.prod_apply, MonoidHom.id_apply, hc] using sub_eq_zero.mpr h)
      have h := congrArg (eval ![u,v]) hz
      simpa only [map_sub, eval_C, he, map_zero, sub_eq_zero] using h
    have hl : ∀ g x, f (rho (g,1) x) = f x :=
      (GeneratorInvariantTests.invariant_iff (rho.comp (MonoidHom.inl G G)) _ hg f).mpr
        (fun az x => by simpa [hzero] using ht az.1 az.2 0 x)
    have hr : ∀ g x, f (rho (1,g) x) = f x :=
      (GeneratorInvariantTests.invariant_iff (rho.comp (MonoidHom.inr G G)) _ hg f).mpr
        (fun az x => by simpa [hzero] using ht az.1 0 az.2 x)
    intro g x
    have he : g = (g.1,1) * (1,g.2) := by simp
    rw [he, map_mul, Module.End.mul_apply, hl, hr]
  · intro hf g x
    exact hf _ x

theorem fixed_iff_action (hg : Subgroup.closure (Set.range (fun az : A × ℂ => family az.1 az.2)) = ⊤)
    (hc : ∀ a z, conjugate (family a z) = family a (star z))
    (hzero : ∀ a, family a 0 = 1) (hp : PolynomialOrbits rho family)
    (sigma : Representation ℂ G V) (he : rho.comp (paired conjugate) = sigma)
    (f : Module.Dual ℂ V) :
    (∀ g x, f (sigma g x) = f x) ↔ ∀ g x, f (rho g x) = f x := by
  have h := fixed_iff rho conjugate family hg hc hzero hp f
  simpa only [← he,MonoidHom.comp_apply] using h

end
end Math.PairedPolynomialInvariants
