import Math.Algebra.Variational.LocalEuler

/-! Formal adjoints depend on the commuting derivative multiindex, not its
chosen ordered word. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
variable {F B I : Type*}
local instance wordDecF : DecidableEq F := Classical.decEq _
local instance wordDecB : DecidableEq B := Classical.decEq _
local instance wordDecI : DecidableEq I := Classical.decEq _
@[reducible] local instance wordAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance wordModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance wordRing : Ring (A F B I) := inferInstance

namespace Expr
@[simp] theorem wordIndex_append (w v : List I) : wordIndex (w++v) = wordIndex w+wordIndex v := by
  induction w with
  | nil => simp [wordIndex]
  | cons i w ih => simp [wordIndex, ih, add_comm, add_left_comm]

theorem wordIndex_count (w : List I) (i : I) : wordIndex w i = w.count i := by
  classical
  induction w with
  | nil => simp [wordIndex]
  | cons j w ih =>
    by_cases h : j = i
    · subst j; simp [wordIndex, ih]
    · simp [wordIndex, ih, h, Ne.symm h]

theorem perm_of_wordIndex_eq {w v : List I} (h : wordIndex w = wordIndex v) : w.Perm v := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  rw [← wordIndex_count, ← wordIndex_count, h]

theorem wordIndex_surjective : Function.Surjective (wordIndex : List I → I →₀ ℕ) := by
  classical
  intro a
  induction a using Finsupp.induction with
  | zero => exact ⟨[],rfl⟩
  | @single_add i n a hi hn ih =>
    obtain ⟨w,rfl⟩ := ih
    refine ⟨List.replicate n i ++ w,?_⟩
    rw [wordIndex_append]
    congr 1
    ext j
    rw [wordIndex_count]
    by_cases h : i = j
    · subst j; simp
    · simp [List.count_replicate, h, Ne.symm h]
end Expr

theorem adjoint_perm {w v : List I} (h : w.Perm v) (p : A F B I) :
    VariationalIBP.adjoint D w p = VariationalIBP.adjoint D v p := by
  induction h generalizing p with
  | nil => rfl
  | cons i h ih => exact ih _
  | swap i j w =>
    simp only [VariationalIBP.adjoint, map_neg, neg_neg, D,
      MixedJetAlgebra.totalDerivative_commute i j]
  | trans h k hh hk => exact (hh p).trans (hk p)

def indexAdjoint (a : I →₀ ℕ) : A F B I →ₗ[ℂ] A F B I where
  toFun p := VariationalIBP.adjoint D (Classical.choose (Expr.wordIndex_surjective a)) p
  map_add' p q := by
    generalize Classical.choose (Expr.wordIndex_surjective a) = w
    induction w generalizing p q with
    | nil => rfl
    | cons i w ih => simp only [VariationalIBP.adjoint, map_add, neg_add, ih]
  map_smul' c p := VariationalIBP.adjoint_smul D _ c p

theorem indexAdjoint_word (w : List I) (p : A F B I) :
    indexAdjoint (Expr.wordIndex w) p = VariationalIBP.adjoint D w p := by
  apply adjoint_perm
  apply Expr.perm_of_wordIndex_eq
  exact Classical.choose_spec (Expr.wordIndex_surjective (Expr.wordIndex w))

@[simp] theorem indexAdjoint_zero (p : A F B I) : indexAdjoint (0 : I →₀ ℕ) p = p :=
  indexAdjoint_word [] p

theorem indexAdjoint_shift (a : I →₀ ℕ) (i : I) (p : A F B I) :
    indexAdjoint (a+Finsupp.single i 1) p = indexAdjoint a (-D i p) := by
  obtain ⟨w,rfl⟩ := Expr.wordIndex_surjective a
  exact (indexAdjoint_word (i::w) p).trans (indexAdjoint_word w (-D i p)).symm

end
end Math.LocalPolynomial
