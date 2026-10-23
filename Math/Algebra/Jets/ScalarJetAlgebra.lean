import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Analysis.Complex.Basic

/-! Ordinary, off-shell scalar jets with commuting formal total derivatives.
No highest jet is truncated, and no equation of motion is imposed. -/
namespace Math.ScalarJetAlgebra
set_option autoImplicit false
noncomputable section
open MvPolynomial

abbrev Index (S I : Type*) := S × (I →₀ ℕ)
abbrev Algebra (S I : Type*) := MvPolynomial (Index S I) ℂ

variable {S T I : Type*}

def order (a : I →₀ ℕ) : ℕ := Finsupp.weight (fun _ : I => 1) a

def weight (j : Index S I) : ℕ × ℕ := (1, order j.2)

def shift (i : I) (j : Index S I) : Index S I := (j.1, j.2 + Finsupp.single i 1)

@[simp] theorem weight_shift (i : I) (j : Index S I) :
    weight (shift i j) = weight j + (0, 1) := by
  simp [weight, shift, order, map_add, Finsupp.weight_single]

def totalDerivative (i : I) : Derivation ℂ (Algebra S I) (Algebra S I) :=
  MvPolynomial.mkDerivation ℂ (fun j => X (shift i j))

@[simp] theorem totalDerivative_X (i : I) (j : Index S I) :
    totalDerivative i (X j : Algebra S I) = X (shift i j) := by
  simp [totalDerivative]

theorem totalDerivative_mul (i : I) (p q : Algebra S I) :
    totalDerivative i (p * q) = p * totalDerivative i q + q * totalDerivative i p :=
  (totalDerivative i).leibniz p q

theorem totalDerivative_commute (i j : I) (p : Algebra S I) :
    totalDerivative i (totalDerivative j p) = totalDerivative j (totalDerivative i p) := by
  have h : ⁅totalDerivative (S := S) i, totalDerivative (S := S) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro x
    simp [Derivation.commutator_apply, shift, add_comm, add_left_comm]
  exact sub_eq_zero.mp (DFunLike.congr_fun h p)

def relabel (f : S → T) : Algebra S I →ₐ[ℂ] Algebra T I :=
  MvPolynomial.rename (fun j => (f j.1, j.2))

@[simp] theorem relabel_X (f : S → T) (j : Index S I) :
    relabel f (X j) = X (f j.1, j.2) := by simp [relabel]

theorem totalDerivative_relabel (f : S → T) (i : I) (p : Algebra S I) :
    totalDerivative i (relabel f p) = relabel f (totalDerivative i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [relabel]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, totalDerivative_mul, relabel_X, totalDerivative_X, map_add, hp]
    rfl

def grade (n d : ℕ) : Submodule ℂ (Algebra S I) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ weight (n, d)

theorem totalDerivative_homogeneous (i : I) {g : ℕ × ℕ} {p : Algebra S I}
    (hp : p.IsWeightedHomogeneous weight g) :
    (totalDerivative i p).IsWeightedHomogeneous weight (g + (0, 1)) := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero ℂ weight (g + (0, 1))
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial a c ha =>
    rw [totalDerivative, MvPolynomial.mkDerivation_monomial]
    apply (MvPolynomial.weightedHomogeneousSubmodule ℂ weight (g + (0, 1))).smul_mem c
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hj
    have hw : Finsupp.weight weight (a - Finsupp.single j 1) + weight j = g := by
      rw [Finsupp.weight_sub_single_add (Finsupp.mem_support_iff.mp hj), ha]
    have h := (MvPolynomial.isWeightedHomogeneous_monomial weight
      (a - Finsupp.single j 1) (a j : ℂ) rfl).mul
        (MvPolynomial.isWeightedHomogeneous_X ℂ weight (shift i j))
    rw [weight_shift, ← add_assoc, hw] at h
    exact h

theorem totalDerivative_mem (i : I) {n d : ℕ} {p : Algebra S I}
    (hp : p ∈ grade n d) : totalDerivative i p ∈ grade n (d + 1) :=
  totalDerivative_homogeneous i hp

end
end Math.ScalarJetAlgebra
