import Math.RepresentationTheory.Relations.RelationQuotient
import Math.RepresentationTheory.Relations.FiniteStatisticalFactor

/-! A residual coefficient family is the equivariant dual of a direct sum of
flavor inputs. Independently computed local exchange matrices generate an
actual relation module in that direct sum. -/
namespace Math.ResidualRelationPresentation
set_option autoImplicit false
noncomputable section
open Representation

variable {H X I : Type*} [Group H] [AddCommGroup X] [Module ℂ X]
  (x : Representation ℂ H X)

abbrev Coordinates := I → IntertwiningMap x (Representation.trivial ℂ H ℂ)

def assemble (c : Coordinates (I := I) x) :
    IntertwiningMap (x.finsupp I) (Representation.trivial ℂ H ℂ) where
  toLinearMap := Finsupp.lsum ℂ (fun i => (c i).toLinearMap)
  isIntertwining' g := by
    apply Finsupp.lhom_ext
    intro i w
    simpa using (IntertwiningMap.isIntertwining _ _ (c i) g w)

@[simp] theorem assemble_single (c : Coordinates (I := I) x) (i : I) (w : X) :
    assemble x c (Finsupp.single i w) = c i w := by
  simp [assemble]

def extract (f : IntertwiningMap (x.finsupp I) (Representation.trivial ℂ H ℂ)) :
    Coordinates (I := I) x := fun i => {
  toLinearMap := f.toLinearMap.comp (Finsupp.lsingle i)
  isIntertwining' g := by
    ext w
    simpa using (IntertwiningMap.isIntertwining _ _ f g (Finsupp.single i w)) }

def familyEquiv : Coordinates (I := I) x ≃ₗ[ℂ]
    IntertwiningMap (x.finsupp I) (Representation.trivial ℂ H ℂ) where
  toFun := assemble x
  invFun := extract x
  left_inv c := by funext i; ext w; simp [extract]
  right_inv f := by
    apply IntertwiningMap.ext
    apply Finsupp.lhom_ext
    intro i w
    simp [extract]
  map_add' c d := by
    apply IntertwiningMap.ext
    apply Finsupp.lhom_ext
    intro i w
    simp
  map_smul' z c := by
    apply IntertwiningMap.ext
    apply Finsupp.lhom_ext
    intro i w
    simp

section Exchange
variable {J : Type*} [Fintype I] [DecidableEq I]
  (matrix : J → I → I → ℂ)
  (exchange : J → IntertwiningMap x x) (sign : J → ℂ)

/-- The row index is the extracted probe. This input relation is the transpose
of the corresponding action on coefficient coordinates. -/
def relation (j : J) (i : I) (w : X) : I →₀ X :=
  (∑ m, Finsupp.single m (matrix j i m • exchange j w)) -
    Finsupp.single i (sign j • w)

def relations : Submodule ℂ (I →₀ X) :=
  RelationQuotient.relations (fun t : J × I × X => relation x matrix exchange sign t.1 t.2.1 t.2.2)

omit [DecidableEq I] in
theorem relation_mem (j : J) (i : I) (w : X) :
    relation x matrix exchange sign j i w ∈ relations x matrix exchange sign :=
  Submodule.subset_span ⟨(j, i, w), rfl⟩

omit [DecidableEq I] in
theorem relation_action (g : H) (j : J) (i : I) (w : X) :
    x.finsupp I g (relation x matrix exchange sign j i w) =
      relation x matrix exchange sign j i (x g w) := by
  simp [relation, IntertwiningMap.isIntertwining _ _ (exchange j) g w]

omit [DecidableEq I] in
theorem stable : ∀ g, relations x matrix exchange sign ≤
    (relations x matrix exchange sign).comap (x.finsupp I g) := by
  apply RelationQuotient.relations_stable
  intro g t
  rw [relation_action]
  exact relation_mem x matrix exchange sign _ _ _

def quotientRepresentation :=
  (x.finsupp I).quotient (relations x matrix exchange sign) (stable x matrix exchange sign)

def sector : Submodule ℂ (Coordinates (I := I) x) where
  carrier := {c | ∀ j i w,
    (∑ m, matrix j i m * c m (exchange j w)) = sign j * c i w}
  zero_mem' := by intro j i w; simp
  add_mem' := by
    intro c d hc hd j i w
    change (∑ m, matrix j i m * (c m (exchange j w) + d m (exchange j w))) =
      sign j * (c i w + d i w)
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hc j i w, hd j i w]
  smul_mem' := by
    intro z c hc j i w
    simp only [Pi.smul_apply, IntertwiningMap.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (matrix _ _ _) z, mul_assoc]
    rw [← Finset.mul_sum, hc j i w]
    ring

omit [DecidableEq I] in
theorem admissible (c : Coordinates (I := I) x) :
    c ∈ sector x matrix exchange sign ↔
    familyEquiv x c ∈ RelationQuotient.vanishing (x.finsupp I)
      (Representation.trivial ℂ H ℂ) (relations x matrix exchange sign) := by
  unfold relations
  rw [RelationQuotient.vanish_relations_iff]
  change (∀ j i w, _) ↔ ∀ t : J × I × X,
    assemble x c (relation x matrix exchange sign t.1 t.2.1 t.2.2) = 0
  simp only [relation, map_sub, map_sum, assemble_single, map_smul,
    smul_eq_mul, sub_eq_zero]
  constructor
  · intro h t; exact h t.1 t.2.1 t.2.2
  · intro h j i w; exact h (j, i, w)

/-- Explicit residual-Hom classification of exchange-constrained coordinate
families. Arbitrary flavor dimension and arbitrary residual groups are allowed. -/
def equiv : sector x matrix exchange sign ≃ₗ[ℂ]
    IntertwiningMap (quotientRepresentation x matrix exchange sign)
      (Representation.trivial ℂ H ℂ) :=
  (ConstrainedCompleteness.Presentation.mk (familyEquiv x)
    (admissible x matrix exchange sign)).equiv.trans
      (RelationQuotient.equiv (x.finsupp I) (Representation.trivial ℂ H ℂ)
        (relations x matrix exchange sign) (stable x matrix exchange sign))

omit [DecidableEq I] in
@[simp] theorem equiv_single (c : sector x matrix exchange sign) (i : I) (w : X) :
    equiv x matrix exchange sign c
      ((relations x matrix exchange sign).mkQ (Finsupp.single i w)) = c.val i w := by
  change assemble x c.val (Finsupp.single i w) = _
  exact assemble_single x c.val i w

end Exchange
end
end Math.ResidualRelationPresentation
