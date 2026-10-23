import Math.Algebra.Jets.ScalarJetAlgebra
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Joint field/derivative grading of the unbounded scalar jet algebra. -/
namespace Math.ScalarJetAlgebra
set_option autoImplicit false
noncomputable section
open MvPolynomial

variable {S T I : Type*}

theorem weight_relabel (f : S → T) (a : Index S I →₀ ℕ) :
    Finsupp.weight weight (a.mapDomain (fun j => (f j.1, j.2))) = Finsupp.weight weight a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [Finsupp.mapDomain_add, map_add, ha, hb]
  | single j k => simp [Finsupp.mapDomain_single, Finsupp.weight_single, weight]

theorem relabel_homogeneous (f : S → T) {g : ℕ × ℕ} {p : Algebra S I}
    (hp : p.IsWeightedHomogeneous weight g) :
    (relabel f p).IsWeightedHomogeneous weight g := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero ℂ weight g
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial a c ha =>
    rw [relabel, MvPolynomial.rename_monomial]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    exact (weight_relabel f a).trans ha

theorem weight_fst (a : Index S I →₀ ℕ) :
    (Finsupp.weight weight a).1 = Finsupp.weight (fun _ : Index S I => 1) a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Prod.fst_add, ha, hb]
  | single j k => simp [Finsupp.weight_single, weight]

theorem weight_snd (a : Index S I →₀ ℕ) :
    (Finsupp.weight weight a).2 = Finsupp.weight (fun j : Index S I => order j.2) a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Prod.snd_add, ha, hb]
  | single j k => simp [Finsupp.weight_single, weight]

theorem exponent_bound {n d : ℕ} {a : Index S I →₀ ℕ}
    (ha : Finsupp.weight weight a = (n, d)) (j : Index S I) : a j ≤ n := by
  have h := Finsupp.le_weight (fun _ : Index S I => 1) (s := j) (by decide) a
  rwa [← weight_fst, ha] at h

theorem jet_order_bound {n d : ℕ} {a : Index S I →₀ ℕ}
    (ha : Finsupp.weight weight a = (n, d)) {j : Index S I} (hj : a j ≠ 0) :
    order j.2 ≤ d := by
  have h := Finsupp.le_weight_of_ne_zero' (fun j : Index S I => order j.2) hj
  rwa [← weight_snd, ha] at h

theorem finite_monomials [Finite S] [Finite I] (n d : ℕ) :
    {a : Index S I →₀ ℕ | Finsupp.weight weight a = (n, d)}.Finite := by
  classical
  let A := {a : I →₀ ℕ // order a ≤ d}
  have hA : Finite A := (Finsupp.finite_of_nat_weight_le (fun _ : I => 1)
    (fun _ => by decide) d).to_subtype
  let J := {j : Index S I // order j.2 ≤ d}
  have hJ : Finite J := Finite.of_injective
    (fun j : J => (j.val.1, (⟨j.val.2, j.property⟩ : A))) (by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x : S × A => x.1) h
      · exact congrArg (fun x : S × A => x.2.val) h)
  let E := {a : Index S I →₀ ℕ // Finsupp.weight weight a = (n, d)}
  let encode (a : E) (j : J) : Fin (n + 1) :=
    ⟨a.val j.val, Nat.lt_succ_of_le (exponent_bound a.property j.val)⟩
  have hi : Function.Injective encode := by
    intro a b h
    apply Subtype.ext
    ext j
    by_cases hj : order j.2 ≤ d
    · exact congrArg Fin.val (congrFun h ⟨j, hj⟩)
    · have ha : a.val j = 0 := by
        by_contra ha
        exact hj (jet_order_bound a.property ha)
      have hb : b.val j = 0 := by
        by_contra hb
        exact hj (jet_order_bound b.property hb)
      rw [ha, hb]
  have : Finite E := Finite.of_injective encode hi
  exact Set.toFinite _

instance grade_finiteDimensional [Finite S] [Finite I] (n d : ℕ) :
    FiniteDimensional ℂ (grade (S := S) (I := I) n d) := by
  unfold grade
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials (S := S) (I := I) n d).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ
    {a : Index S I →₀ ℕ | Finsupp.weight weight a = (n, d)})

def derivative (i : I) (n d : ℕ) :
    grade (S := S) (I := I) n d →ₗ[ℂ] grade (S := S) (I := I) n (d + 1) where
  toFun p := ⟨totalDerivative i p.val, totalDerivative_mem i p.property⟩
  map_add' p q := Subtype.ext (map_add (totalDerivative i) p.val q.val)
  map_smul' c p := Subtype.ext ((totalDerivative i).toLinearMap.map_smul c p.val)

@[simp] theorem derivative_apply (i : I) (n d : ℕ) (p : grade (S := S) (I := I) n d) :
    (derivative i n d p).val = totalDerivative i p.val := rfl

def relabelGrade (f : S → T) (n d : ℕ) :
    grade (S := S) (I := I) n d →ₗ[ℂ] grade (S := T) (I := I) n d where
  toFun p := ⟨relabel f p.val, relabel_homogeneous f p.property⟩
  map_add' p q := Subtype.ext (map_add (relabel f) p.val q.val)
  map_smul' c p := Subtype.ext ((relabel f).toLinearMap.map_smul c p.val)

theorem derivative_relabelGrade (f : S → T) (i : I) (n d : ℕ)
    (p : grade (S := S) (I := I) n d) :
    derivative i n d (relabelGrade f n d p) =
      relabelGrade f n (d + 1) (derivative i n d p) :=
  Subtype.ext (totalDerivative_relabel f i p.val)

def multiply {n d m e : ℕ} (p : grade (S := S) (I := I) n d)
    (q : grade (S := S) (I := I) m e) : grade (S := S) (I := I) (n + m) (d + e) :=
  ⟨p.val * q.val, p.property.mul q.property⟩

def productLeft (i : I) {n d m e : ℕ} (p : grade (S := S) (I := I) n d)
    (q : grade (S := S) (I := I) m e) : grade (S := S) (I := I) (n + m) (d + e + 1) :=
  ⟨p.val * totalDerivative i q.val, by
    change MvPolynomial.IsWeightedHomogeneous weight _ (n + m, d + e + 1)
    have h := p.property.mul (totalDerivative_mem i q.property)
    change MvPolynomial.IsWeightedHomogeneous weight _ (n + m, d + (e + 1)) at h
    simpa only [Nat.add_assoc] using h⟩

def productRight (i : I) {n d m e : ℕ} (p : grade (S := S) (I := I) n d)
    (q : grade (S := S) (I := I) m e) : grade (S := S) (I := I) (n + m) (d + e + 1) :=
  ⟨q.val * totalDerivative i p.val, by
    change MvPolynomial.IsWeightedHomogeneous weight _ (n + m, d + e + 1)
    have h := q.property.mul (totalDerivative_mem i p.property)
    change MvPolynomial.IsWeightedHomogeneous weight _ (m + n, e + (d + 1)) at h
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h⟩

theorem derivative_multiply (i : I) {n d m e : ℕ} (p : grade (S := S) (I := I) n d)
    (q : grade (S := S) (I := I) m e) :
    derivative i (n + m) (d + e) (multiply p q) = productLeft i p q + productRight i p q :=
  Subtype.ext (totalDerivative_mul i p.val q.val)

end
end Math.ScalarJetAlgebra
