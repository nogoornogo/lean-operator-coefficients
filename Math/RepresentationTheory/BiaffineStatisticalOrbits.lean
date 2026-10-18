import Math.RepresentationTheory.PairedPolynomialInvariants
import Math.RepresentationTheory.PatternExteriorSource

/-! Explicit bivariate orbit polynomials for chirality-labelled affine slots. -/
namespace Math.BiaffineStatisticalOrbits
set_option autoImplicit false
noncomputable section
open Representation MvPolynomial
open scoped TensorProduct BigOperators

def PolynomialFunction (h : ℂ → ℂ → ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℂ, ∀ u v, eval ![u,v] p = h u v

theorem add {h k : ℂ → ℂ → ℂ} (hh : PolynomialFunction h) (hk : PolynomialFunction k) :
    PolynomialFunction (fun u v => h u v + k u v) := by
  obtain ⟨p,hp⟩ := hh
  obtain ⟨q,hq⟩ := hk
  exact ⟨p+q, by simp [hp,hq]⟩

theorem smul {h : ℂ → ℂ → ℂ} (hh : PolynomialFunction h) (c : ℂ) :
    PolynomialFunction (fun u v => c * h u v) := by
  obtain ⟨p,hp⟩ := hh
  exact ⟨C c * p, by simp [hp]⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem multilinear_affine (f : MultilinearMap ℂ V ℂ) (right : ι → Bool) (x y : ∀ i, V i) :
    PolynomialFunction (fun u v => f (fun i => x i + (if right i then v else u) • y i)) := by
  let p : MvPolynomial (Fin 2) ℂ := ∑ s : Finset ι,
    C (f (s.piecewise y x)) * ∏ i ∈ s, X (if right i then 1 else 0)
  refine ⟨p, ?_⟩
  intro u v
  have hs (s : Finset ι) : f (s.piecewise (fun i => (if right i then v else u) • y i) x) =
      (∏ i ∈ s, if right i then v else u) * f (s.piecewise y x) := by
    have hv : s.piecewise (fun i => (if right i then v else u) • y i) x =
        fun i => (if i ∈ s then (if right i then v else u) else 1) • s.piecewise y x i := by
      funext i; by_cases hi : i ∈ s <;> simp [Finset.piecewise,hi]
    rw [hv, f.map_smul_univ]
    simp [smul_eq_mul]
  have hv : (fun i => x i + (if right i then v else u) • y i) =
      (fun i => (if right i then v else u) • y i) + x := by funext i; simp [add_comm]
  change eval ![u,v] p = f (fun i => x i + (if right i then v else u) • y i)
  rw [hv, f.map_add_univ]
  simp_rw [hs]
  simp only [p, map_sum, map_mul, eval_C, map_prod, eval_X]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases right i <;> simp

variable {G A : Type*} [Group G] (r : ∀ i, Representation ℂ (G × G) (V i))
  (family : A → ℂ → G)

def Affine (right : ι → Bool) : Prop := ∀ a i x, ∃ y, ∀ u v,
  r i (family a u,family a v) x = x + (if right i then v else u) • y

theorem raw_polynomial (right : ι → Bool) (ha : Affine r family right) :
    PairedPolynomialInvariants.PolynomialOrbits
      (MultilinearInvariantHom.tensorRepresentation r) family := by
  intro a f x
  change PolynomialFunction (fun u v => f (MultilinearInvariantHom.tensorRepresentation r
    (family a u,family a v) x))
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    choose y hy using fun i => ha a i (w i)
    obtain ⟨p,hp⟩ := smul (multilinear_affine
      (f.compMultilinearMap (PiTensorProduct.tprod ℂ)) right w y) c
    refine ⟨p, ?_⟩
    intro u v
    simpa [MultilinearInvariantHom.tensorRepresentation_tprod,hy] using hp u v
  | add x y hx hy =>
    obtain ⟨p,hp⟩ := add hx hy
    exact ⟨p, by intro u v; simpa using hp u v⟩

variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

theorem descend (rho : Representation ℂ (G × G) U) (sigma : Representation ℂ (G × G) W)
    (e : IntertwiningMap rho sigma) (he : Function.Surjective e)
    (hp : PairedPolynomialInvariants.PolynomialOrbits rho family) :
    PairedPolynomialInvariants.PolynomialOrbits sigma family := by
  intro a f y
  obtain ⟨x,rfl⟩ := he y
  obtain ⟨p,hp⟩ := hp a (f.comp e.toLinearMap) x
  refine ⟨p, ?_⟩
  intro u v
  rw [← e.isIntertwining rho sigma (family a u,family a v) x]
  exact hp u v

theorem tensor_fixed (rho : Representation ℂ (G × G) U) (sigma : Representation ℂ (G × G) W)
    (hp : PairedPolynomialInvariants.PolynomialOrbits rho family)
    (hs : ∀ a u v y, sigma (family a u,family a v) y = y) :
    PairedPolynomialInvariants.PolynomialOrbits (rho.tprod sigma) family := by
  intro a f x
  change PolynomialFunction (fun u v => f ((rho.tprod sigma) (family a u,family a v) x))
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨p,hp⟩ := hp a (f.comp ((TensorProduct.mk ℂ U W).flip y)) x
    exact ⟨p, by intro u v; simpa [Representation.tprod_apply,hs] using hp u v⟩
  | add x y hx hy =>
    obtain ⟨p,hp⟩ := add hx hy
    exact ⟨p, by intro u v; simpa using hp u v⟩

end
end Math.BiaffineStatisticalOrbits
