import Math.Algebra.Jets.DifferentialEquationIdeal
import Math.RepresentationTheory.Jets.NonlinearJetIBP
import Mathlib.Data.Matrix.Mul

/-! Engineering degree with component dimension one and derivative dimension
one. Quotient image spaces are finite without claiming a global direct sum. -/
namespace Math.JetEngineering
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {S I : Type*}

def weight (j : Index S I) : ℕ := 1 + order j.2
def grade (S I : Type*) (k : ℕ) : Submodule ℂ (Algebra S I) :=
  weightedHomogeneousSubmodule ℂ weight k

@[simp] theorem weight_shift (i : I) (j : Index S I) : weight (shift i j) = weight j + 1 := by
  simp [weight, shift, order, map_add, Finsupp.weight_single]
  omega

theorem finite_monomials [Finite S] [Finite I] (k : ℕ) :
    {a : Index S I →₀ ℕ | Finsupp.weight weight a = k}.Finite := by
  classical
  let J := {j : Index S I // order j.2 ≤ k}
  have hA : Finite {a : I →₀ ℕ // order a ≤ k} :=
    (Finsupp.finite_of_nat_weight_le (fun _ : I => 1) (fun _ => by decide) k).to_subtype
  have hJ : Finite J := Finite.of_injective
    (fun j : J => (j.val.1, (⟨j.val.2, j.property⟩ : {a : I →₀ ℕ // order a ≤ k}))) (by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x : S × {a : I →₀ ℕ // order a ≤ k} => x.1) h
      · exact congrArg (fun x : S × {a : I →₀ ℕ // order a ≤ k} => x.2.val) h)
  let E := {a : Index S I →₀ ℕ // Finsupp.weight weight a = k}
  have hb (a : E) (j : Index S I) : a.val j ≤ k := by
    have h := Finsupp.le_weight weight (s := j) (show weight j ≠ 0 by dsimp [weight]; omega) a.val
    simpa only [a.property] using h
  let encode (a : E) (j : J) : Fin (k + 1) := ⟨a.val j.val, Nat.lt_succ_of_le (hb a j.val)⟩
  have hi : Function.Injective encode := by
    intro a b h
    apply Subtype.ext
    ext j
    by_cases hj : order j.2 ≤ k
    · exact congrArg Fin.val (congrFun h ⟨j, hj⟩)
    · have hz (c : E) : c.val j = 0 := by
        by_contra hc
        have hw := Finsupp.le_weight_of_ne_zero' weight hc
        rw [c.property] at hw
        exact hj (by dsimp [weight] at hw; omega)
      rw [hz a, hz b]
  have : Finite E := Finite.of_injective encode hi
  exact Set.toFinite _

instance grade_finite [Finite S] [Finite I] (k : ℕ) : FiniteDimensional ℂ (grade S I k) := by
  unfold grade
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials (S := S) (I := I) k).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

theorem derivative_homogeneous (i : I) {k : ℕ} {p : Algebra S I}
    (hp : p.IsWeightedHomogeneous weight k) :
    (totalDerivative i p).IsWeightedHomogeneous weight (k + 1) := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isWeightedHomogeneous_zero ℂ weight (k + 1)
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial a c ha =>
    rw [totalDerivative, MvPolynomial.mkDerivation_monomial]
    apply (weightedHomogeneousSubmodule ℂ weight (k + 1)).smul_mem c
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hj
    have hw : Finsupp.weight weight (a - Finsupp.single j 1) + weight j = k := by
      rw [Finsupp.weight_sub_single_add (Finsupp.mem_support_iff.mp hj), ha]
    have h := (MvPolynomial.isWeightedHomogeneous_monomial weight
      (a - Finsupp.single j 1) (a j : ℂ) rfl).mul
        (MvPolynomial.isWeightedHomogeneous_X ℂ weight (shift i j))
    rw [weight_shift, ← add_assoc, hw] at h
    exact h

theorem product_homogeneous {k l : ℕ} {p q : Algebra S I}
    (hp : p ∈ grade S I k) (hq : q ∈ grade S I l) : p * q ∈ grade S I (k + l) := hp.mul hq

theorem matrix_product_mem {N : Type*} [Fintype N] [DecidableEq N]
    {k l : ℕ} (x y : Matrix N N (Algebra S I))
    (hx : ∀ a b, x a b ∈ grade S I k) (hy : ∀ a b, y a b ∈ grade S I l) (a b : N) :
    (x * y) a b ∈ grade S I (k + l) := by
  rw [Matrix.mul_apply]
  exact (grade S I (k + l)).sum_mem (fun c _ => (hx a c).mul (hy c b))

variable (R : Set (Algebra S I))

def eomImage (k : ℕ) := DifferentialEquation.image totalDerivative R (grade S I k)
def ibpImage (k : ℕ) := (grade S I k).map (DifferentialEquation.integrated totalDerivative R)

instance eomImage_finite [Finite S] [Finite I] (k : ℕ) : FiniteDimensional ℂ (eomImage R k) := by
  unfold eomImage
  infer_instance

instance ibpImage_finite [Finite S] [Finite I] (k : ℕ) : FiniteDimensional ℂ (ibpImage R k) := by
  unfold ibpImage
  exact Module.Finite.map _ _

end
end Math.JetEngineering
