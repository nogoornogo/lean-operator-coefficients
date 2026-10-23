import Math.RepresentationTheory.Invariants.GeneratorInvariantTests
import Mathlib.Algebra.Polynomial.Roots

/-! Exact polynomial interpolation turns a certified parameter action into
exhaustive finite group tests. Polynomial identities remain explicit inputs. -/
namespace Math.PolynomialInvariantTests
set_option autoImplicit false
noncomputable section
open Polynomial

theorem zero_of_samples {I : Type*} [Fintype I] (samples : I → ℂ)
    (hi : Function.Injective samples) (D : ℕ) (hc : D < Fintype.card I)
    (p : ℂ[X]) (hd : p.natDegree ≤ D) (hp : ∀ i, p.eval (samples i)=0) : p=0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hi hp (hd.trans_lt hc)

theorem grid_zero {I J : Type*} [Fintype I] [Fintype J]
    (xs : I → ℂ) (ys : J → ℂ) (hx : Function.Injective xs) (hy : Function.Injective ys)
    (D E : ℕ) (hD : D < Fintype.card I) (hE : E < Fintype.card J)
    (p : (ℂ[X])[X]) (hp : p.natDegree ≤ D) (hq : ∀ k, (p.coeff k).natDegree ≤ E)
    (hv : ∀ i j, (p.eval (Polynomial.C (xs i))).eval (ys j)=0) : p=0 := by
  have he (j : J) : p.map (Polynomial.evalRingHom (ys j)) = 0 := by
    apply zero_of_samples xs hx D hD
    · exact (Polynomial.natDegree_map_le).trans hp
    · intro i
      have hcomm := Polynomial.hom_eval₂ p (RingHom.id (ℂ[X]))
        (Polynomial.evalRingHom (ys j)) (Polynomial.C (xs i))
      have hev : (p.eval (Polynomial.C (xs i))).eval (ys j) =
          (p.map (Polynomial.evalRingHom (ys j))).eval (xs i) := by
        simpa only [RingHom.comp_id, Polynomial.eval₂_id, Polynomial.eval_C,
          Polynomial.eval_map, Polynomial.coe_evalRingHom] using hcomm
      rw [← hev]
      exact hv i j
  apply Polynomial.ext
  intro k
  apply zero_of_samples ys hy E hE (p.coeff k) (hq k)
  intro j
  have hc := congrArg (fun q : ℂ[X] => q.coeff k) (he j)
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
    Polynomial.coe_evalRingHom] using hc

variable {G V F I : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
  (rho : Representation ℂ G V) (families : F → ℂ → G) (samples : I → ℂ)

def PolynomialAction (D : ℕ) : Prop :=
  ∀ t (f : Module.Dual ℂ V) x, ∃ p : ℂ[X], p.natDegree ≤ D ∧
    ∀ z, p.eval z = f (rho (families t z) x) - f x

omit [Fintype F] [DecidableEq F] [DecidableEq I] in
theorem exhaustive (D : ℕ) (hi : Function.Injective samples) (hc : D < Fintype.card I)
    (hp : PolynomialAction rho families D)
    (hg : Subgroup.closure (Set.range (fun ti : F × ℂ => families ti.1 ti.2)) = ⊤) :
    FiniteInvariantKernel.Exhaustive rho (fun ti : F × I => families ti.1 (samples ti.2)) := by
  intro f hf
  apply (GeneratorInvariantTests.invariant_iff rho _ hg f).mpr
  intro ti x
  obtain ⟨p,hd,he⟩ := hp ti.1 f x
  have hz : p=0 := zero_of_samples samples hi D hc p hd (by
    intro i
    rw [he, hf (ti.1,i), sub_self])
  have hv := he ti.2
  rw [hz, Polynomial.eval_zero] at hv
  exact (sub_eq_zero.mp hv.symm)

end
end Math.PolynomialInvariantTests
