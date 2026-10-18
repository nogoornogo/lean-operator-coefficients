import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

/-!
# Finite-dimensional irreducible `sl₂` strings

This file completes the algebraic step between mathlib's primitive-vector
theory for an `sl₂` triple and the familiar dimension formula.  If the
triple spans the acting Lie algebra and the module is irreducible, the vectors
obtained by repeatedly applying the lowering operator form a basis.
-/

namespace Math
namespace Sl2String

open LieModule Module Set

noncomputable section

variable {L M : Type*}
variable [LieRing L] [LieAlgebra ℂ L]
variable [AddCommGroup M] [Module ℂ M]
variable [LieRingModule L M] [LieModule ℂ L M]
variable {h e f : L} {m : M} {n : ℕ}

/-- The finite lowering string attached to a primitive vector of integral
highest weight `n`. -/
def stringVector (t : IsSl2Triple h e f)
    (_P : t.HasPrimitiveVectorWith m (n : ℂ))
    (i : Fin (n + 1)) : M :=
  ((toEnd ℂ L M f) ^ (i : ℕ)) m

namespace stringVector

variable (t : IsSl2Triple h e f)
variable (P : t.HasPrimitiveVectorWith m (n : ℂ))

theorem ne_zero [FiniteDimensional ℂ M] (i : Fin (n + 1)) :
    stringVector t P i ≠ 0 := by
  apply P.pow_toEnd_f_ne_zero_of_eq_nat (R := ℂ) rfl
  omega

theorem lie_h (i : Fin (n + 1)) :
    ⁅h, stringVector t P i⁆ =
      ((n : ℂ) - 2 * (i : ℕ)) • stringVector t P i := by
  exact P.lie_h_pow_toEnd_f (R := ℂ) (i : ℕ)

end stringVector

/-- Distinct weights of the lowering string make its vectors linearly
independent. -/
theorem stringVector_linearIndependent
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M] :
    LinearIndependent ℂ (stringVector t P) := by
  apply (toEnd ℂ L M h).eigenvectors_linearIndependent'
    (fun i : Fin (n + 1) => (n : ℂ) - 2 * (i : ℕ))
  · intro i j hij
    apply Fin.ext
    have hcast : (i : ℂ) = (j : ℂ) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
      exact sub_right_inj.mp hij
    exact_mod_cast hcast
  · intro i
    constructor
    · rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply]
      exact stringVector.lie_h t P i
    · exact stringVector.ne_zero t P i

/-- The ordinary linear span of the lowering string. -/
def stringSpan
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ)) :
    Submodule ℂ M :=
  Submodule.span ℂ (Set.range (stringVector t P))

theorem stringVector_mem_stringSpan
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    (i : Fin (n + 1)) : stringVector t P i ∈ stringSpan t P :=
  Submodule.subset_span (Set.mem_range_self i)

theorem lie_h_stringVector_mem
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    (i : Fin (n + 1)) : ⁅h, stringVector t P i⁆ ∈ stringSpan t P := by
  rw [stringVector.lie_h t P i]
  exact (stringSpan t P).smul_mem _ (stringVector_mem_stringSpan t P i)

theorem lie_e_stringVector_mem
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    (i : Fin (n + 1)) : ⁅e, stringVector t P i⁆ ∈ stringSpan t P := by
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    change ⁅e, m⁆ ∈ stringSpan t P
    rw [P.lie_e]
    exact (stringSpan t P).zero_mem
  · let j : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
    have hij : (i : ℕ) = (j : ℕ) + 1 := by
      dsimp [j]
      omega
    change ⁅e, ((toEnd ℂ L M f) ^ (i : ℕ)) m⁆ ∈ stringSpan t P
    rw [hij, P.lie_e_pow_succ_toEnd_f]
    exact (stringSpan t P).smul_mem _ (stringVector_mem_stringSpan t P j)

theorem lie_f_stringVector_mem
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M]
    (i : Fin (n + 1)) : ⁅f, stringVector t P i⁆ ∈ stringSpan t P := by
  rw [show ⁅f, stringVector t P i⁆ =
      ((toEnd ℂ L M f) ^ ((i : ℕ) + 1)) m by
    exact P.lie_f_pow_toEnd_f (R := ℂ) (i : ℕ)]
  by_cases hi : (i : ℕ) < n
  · let j : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
    exact stringVector_mem_stringSpan t P j
  · have hin : (i : ℕ) = n := by omega
    rw [hin, P.pow_toEnd_f_eq_zero_of_eq_nat (R := ℂ) rfl]
    exact (stringSpan t P).zero_mem

private theorem lie_generator_mem_of_mem_stringSpan
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M]
    {x : L} {y : M} (hy : y ∈ stringSpan t P)
    (hx : x = h ∨ x = e ∨ x = f) :
    ⁅x, y⁆ ∈ stringSpan t P := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rcases hx with rfl | rfl | rfl
      · exact lie_h_stringVector_mem t P i
      · exact lie_e_stringVector_mem t P i
      · exact lie_f_stringVector_mem t P i
  | zero => simp
  | add y z _ _ hy hz =>
      rw [lie_add]
      exact (stringSpan t P).add_mem hy hz
  | smul c y _ hy =>
      rw [lie_smul]
      exact (stringSpan t P).smul_mem c hy

/-- The lowering string span as a Lie submodule, provided the distinguished
triple spans the acting Lie algebra. -/
def stringLieSubmodule
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M]
    (hSpans : t.toLieSubalgebra ℂ = ⊤) : LieSubmodule ℂ L M where
  __ := stringSpan t P
  lie_mem {x} {y} hy := by
    have hx : x ∈ t.toLieSubalgebra ℂ := by
      rw [hSpans]
      simp
    obtain ⟨a, b, c, rfl⟩ :=
      (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ) (t := t)).mp hx
    rw [add_lie, add_lie, smul_lie, smul_lie, smul_lie]
    exact (stringSpan t P).add_mem
      ((stringSpan t P).add_mem
        ((stringSpan t P).smul_mem a
          (lie_generator_mem_of_mem_stringSpan t P hy (Or.inr (Or.inl rfl))))
        ((stringSpan t P).smul_mem b
          (lie_generator_mem_of_mem_stringSpan t P hy (Or.inr (Or.inr rfl)))))
      ((stringSpan t P).smul_mem c (by
        rw [t.lie_e_f]
        exact lie_generator_mem_of_mem_stringSpan t P hy (Or.inl rfl)))

/-- Irreducibility forces the nonzero lowering-string Lie submodule to be the
whole module. -/
theorem stringSpan_eq_top
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M]
    [LieModule.IsIrreducible ℂ L M]
    (hSpans : t.toLieSubalgebra ℂ = ⊤) :
    stringSpan t P = ⊤ := by
  let N := stringLieSubmodule t P hSpans
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hBot | hTop
  · exfalso
    apply P.ne_zero
    have hm : m ∈ N := by
      change m ∈ stringSpan t P
      simpa [stringVector] using
        (stringVector_mem_stringSpan t P (0 : Fin (n + 1)))
    rw [hBot] at hm
    exact hm
  · have hSubmodule := congrArg LieSubmodule.toSubmodule hTop
    simpa [N, stringLieSubmodule] using hSubmodule

/-- The standard dimension formula for a finite-dimensional irreducible
module generated by an `sl₂` triple. -/
theorem finrank_eq_highestWeight_add_one
    (t : IsSl2Triple h e f)
    (P : t.HasPrimitiveVectorWith m (n : ℂ))
    [FiniteDimensional ℂ M]
    [LieModule.IsIrreducible ℂ L M]
    (hSpans : t.toLieSubalgebra ℂ = ⊤) :
    Module.finrank ℂ M = n + 1 := by
  let b : Module.Basis (Fin (n + 1)) ℂ M :=
    Module.Basis.mk (stringVector_linearIndependent t P) (by
      simpa [stringSpan] using (stringSpan_eq_top t P hSpans).ge)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- Every finite-dimensional irreducible module for a Lie algebra spanned by
an `sl₂` triple has an integral highest weight and the expected dimension. -/
theorem exists_highestWeight_and_dimension
    (t : IsSl2Triple h e f)
    [FiniteDimensional ℂ M]
    [LieModule.IsIrreducible ℂ L M]
    (hSpans : t.toLieSubalgebra ℂ = ⊤) :
    ∃ (n : ℕ) (m : M),
      t.HasPrimitiveVectorWith m (n : ℂ) ∧
        Module.finrank ℂ M = n + 1 := by
  let : Nontrivial M := LieModule.nontrivial_of_isIrreducible ℂ L M
  let : IsTriangularizable ℂ L M :=
    LieModule.instIsTriangularizableOfIsAlgClosed ℂ L M
  obtain ⟨μ, m, _hm, P⟩ :=
    t.exists_hasPrimitiveVectorWith (R := ℂ) (M := M)
  obtain ⟨n, hn⟩ := P.exists_nat (R := ℂ)
  rw [hn] at P
  exact ⟨n, m, P, finrank_eq_highestWeight_add_one t P hSpans⟩

end

end Sl2String
end Math
