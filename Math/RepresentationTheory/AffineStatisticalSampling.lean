import Math.RepresentationTheory.PolynomialInvariantTests
import Math.RepresentationTheory.PatternExteriorSource
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Bounded exact real-parameter sampling through affine multilinear sources. -/
namespace Math.AffineStatisticalSampling
set_option autoImplicit false
noncomputable section
open Polynomial Representation
open scoped TensorProduct

def PolynomialFunction (D : ℕ) (h : ℝ → ℂ) : Prop :=
  ∃ p : ℂ[X], p.natDegree ≤ D ∧ ∀ t : ℝ, p.eval (t : ℂ) = h t

theorem zero (D : ℕ) : PolynomialFunction D (fun _ => 0) :=
  ⟨0, by simp, by simp⟩
theorem add {D : ℕ} {h k : ℝ → ℂ} (hh : PolynomialFunction D h)
    (hk : PolynomialFunction D k) : PolynomialFunction D (fun t => h t + k t) := by
  obtain ⟨p,hp,he⟩ := hh
  obtain ⟨q,hq,hf⟩ := hk
  exact ⟨p+q, Polynomial.natDegree_add_le_of_degree_le hp hq, by simp [he,hf]⟩
theorem smul {D : ℕ} {h : ℝ → ℂ} (hh : PolynomialFunction D h) (c : ℂ) :
    PolynomialFunction D (fun t => c * h t) := by
  obtain ⟨p,hp,he⟩ := hh
  exact ⟨Polynomial.C c * p, (Polynomial.natDegree_C_mul_le c p).trans hp, by simp [he]⟩
theorem constant (D : ℕ) (c : ℂ) : PolynomialFunction D (fun _ => c) :=
  ⟨Polynomial.C c, by simp, by simp⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- An explicit subset expansion, with degree bounded by the number of slots. -/
theorem multilinear_affine (f : MultilinearMap ℂ V ℂ) (x y : ∀ i, V i) :
    PolynomialFunction (Fintype.card ι) (fun t => f (fun i => x i + (t : ℂ) • y i)) := by
  classical
  let p : ℂ[X] := ∑ s : Finset ι, Polynomial.monomial s.card (f (s.piecewise y x))
  refine ⟨p, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    exact (Polynomial.natDegree_monomial_le _).trans (Finset.card_le_univ s)
  · intro t
    have hs (s : Finset ι) :
        f (s.piecewise (fun i => (t : ℂ) • y i) x) =
          (t : ℂ)^s.card * f (s.piecewise y x) := by
      have hv : s.piecewise (fun i => (t : ℂ) • y i) x =
          fun i => (if i ∈ s then (t : ℂ) else 1) • s.piecewise y x i := by
        funext i
        by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
      rw [hv, f.map_smul_univ]
      simp [smul_eq_mul]
    have hv : (fun i => x i + (t : ℂ) • y i) =
        (fun i => (t : ℂ) • y i) + x := by funext i; simp [add_comm]
    change p.eval (t : ℂ) = f (fun i => x i + (t : ℂ) • y i)
    rw [hv, f.map_add_univ]
    simp_rw [hs]
    simp [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]

variable {G : Type*} [Group G] (r : ∀ i, Representation ℂ G (V i))
  (family : ℝ → G)

/-- Each actual field action is affine in one real parameter. -/
def Affine : Prop := ∀ i x, ∃ y, ∀ t, r i (family t) x = x + (t : ℂ) • y

theorem raw_polynomial (ha : Affine r family)
    (f : Module.Dual ℂ (⨂[ℂ] i, V i)) (x : ⨂[ℂ] i, V i) :
    PolynomialFunction (Fintype.card ι)
      (fun t => f (MultilinearInvariantHom.tensorRepresentation r (family t) x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    choose y hy using fun i => ha i (v i)
    have he := multilinear_affine
      (f.compMultilinearMap (PiTensorProduct.tprod ℂ)) v y
    obtain ⟨p,hp,he'⟩ := smul he c
    refine ⟨p,hp,?_⟩
    intro t
    simpa [MultilinearInvariantHom.tensorRepresentation_tprod, hy] using he' t
  | add x y hx hy =>
    obtain ⟨p,hp,he⟩ := add hx hy
    exact ⟨p,hp, by intro t; simpa using he t⟩

variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def PolynomialOrbits (rho : Representation ℂ G U) (D : ℕ) : Prop :=
  ∀ (f : Module.Dual ℂ U) x, PolynomialFunction D (fun t => f (rho (family t) x))

theorem descend (rho : Representation ℂ G U) (sigma : Representation ℂ G W)
    (e : IntertwiningMap rho sigma) (he : Function.Surjective e) (D : ℕ)
    (hp : PolynomialOrbits family rho D) : PolynomialOrbits family sigma D := by
  intro f y
  obtain ⟨x,rfl⟩ := he y
  obtain ⟨p,hd,hv⟩ := hp (f.comp e.toLinearMap) x
  refine ⟨p,hd,?_⟩
  intro t
  change p.eval (t : ℂ) = f (sigma (family t) (e x))
  rw [← e.isIntertwining rho sigma (family t) x]
  exact hv t

theorem tensor_fixed (rho : Representation ℂ G U) (sigma : Representation ℂ G W)
    (D : ℕ) (hp : PolynomialOrbits family rho D)
    (hs : ∀ t y, sigma (family t) y = y) :
    PolynomialOrbits family (rho.tprod sigma) D := by
  intro f x
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    have he := hp (f.comp ((TensorProduct.mk ℂ U W).flip y)) x
    obtain ⟨p,hd,hv⟩ := he
    refine ⟨p,hd,?_⟩
    intro t
    simpa [Representation.tprod_apply, hs] using hv t
  | add x y hx hy =>
    obtain ⟨p,hd,hv⟩ := add hx hy
    exact ⟨p,hd, by intro t; simpa using hv t⟩

variable {S : Type*} [Fintype S] [DecidableEq S]
  {Fields : S → Type*} [∀ s, AddCommGroup (Fields s)] [∀ s, Module ℂ (Fields s)]

theorem statistical_source (fields : ∀ s, Representation ℂ G (Fields s))
    {n : ℕ} (pattern : Fin n → S)
    (ha : Affine (fun i => fields (pattern i)) family) :
    PolynomialOrbits family (PatternExteriorSource.representation fields pattern) n := by
  apply descend family (PatternExteriorSource.Raw fields pattern)
    (PatternExteriorSource.representation fields pattern)
    (PatternExteriorSource.onto fields pattern)
    (PatternExteriorSource.onto_surjective fields pattern) n
  intro f x
  simpa using raw_polynomial (fun i => fields (pattern i)) family ha f x

/-- Exact natural-number real samples, with a certified distinct complex image. -/
def samples (D : ℕ) (i : Fin (D+1)) : ℝ := i.val

theorem samples_injective (D : ℕ) :
    Function.Injective (fun i : Fin (D+1) => (samples D i : ℂ)) := by
  intro i j hij
  apply Fin.ext
  simp only [samples] at hij
  exact_mod_cast hij

/-- Degree-D orbits need only D+1 exact real samples to test a family. -/
theorem family_invariant (rho : Representation ℂ G U) (D : ℕ)
    (hp : PolynomialOrbits family rho D) (f : Module.Dual ℂ U)
    (hf : ∀ i x, f (rho (family (samples D i)) x) = f x) :
    ∀ t x, f (rho (family t) x) = f x := by
  intro t x
  obtain ⟨p,hd,hv⟩ := add (hp f x) (constant D (-f x))
  have hz : p=0 := PolynomialInvariantTests.zero_of_samples
    (fun i : Fin (D+1) => (samples D i : ℂ)) (samples_injective D) D (by simp) p hd
    (by intro i; rw [hv]; dsimp only; rw [hf]; simp)
  have he := hv t
  rw [hz, Polynomial.eval_zero] at he
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using he.symm)

end
end Math.AffineStatisticalSampling