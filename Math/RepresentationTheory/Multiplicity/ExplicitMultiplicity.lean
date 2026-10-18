import Math.RepresentationTheory.Multiplicity.HilbertMultiplicityOperator
import Math.RepresentationTheory.Multiplicity.UnitaryCentralizerTransport
import Mathlib.RepresentationTheory.Irreducible

/-!
# Commuting operators on named irreducible multiplicity blocks

The abstract multiplicity classification chooses its simple constituents.
Here the constituents are supplied as actual, pairwise inequivalent irreducible
representations. Schur's lemma identifies each copy-to-copy matrix entry;
the existing Hilbert amplification API supplies adjoints and unitarity.
-/

set_option autoImplicit false

namespace Math.ExplicitMultiplicity

noncomputable section

variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
  (m : I → ℕ) (S : I → Type*)
  [∀ i, NormedAddCommGroup (S i)] [∀ i, InnerProductSpace ℂ (S i)]
  (rho : ∀ i, Representation ℂ G (S i))

abbrev Space := HilbertMultiplicityOperator.Space m S
abbrev Matrices := HilbertMultiplicityOperator.Matrices m

def action : Representation ℂ G (Space m S) where
  toFun g :=
    { toFun := fun x => WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => rho i g (x i a)
      map_add' := by intros; ext i a; exact map_add _ _ _
      map_smul' := by intros; ext i a; exact map_smul _ _ _ }
  map_one' := by ext x i a; exact congrArg (fun f => f (x i a)) (rho i).map_one
  map_mul' g h := by ext x i a; exact congrArg (fun f => f (x i a)) ((rho i).map_mul g h)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem action_apply (g : G) (x : Space m S) (i : I) (a : Fin (m i)) :
    action m S rho g x i a = rho i g (x i a) := rfl

omit [DecidableEq I] in
theorem action_unitary (h : ∀ i, UnitaryMultiplicity.IsUnitaryRepresentation (rho i)) :
    UnitaryMultiplicity.IsUnitaryRepresentation (action m S rho) := by
  intro g x y
  simp only [PiLp.inner_apply, action_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl fun a _ => h i g (x i a) (y i a)

def insert (i : I) (a : Fin (m i)) : S i →ₗ[ℂ] Space m S where
  toFun v := PiLp.single 2 i (PiLp.single 2 a v)
  map_add' := by intros; simp [PiLp.single_add]
  map_smul' := by
    intros
    simp only [PiLp.single, Pi.single_smul, WithLp.toLp_smul, RingHom.id_apply]

omit [Fintype I] in
@[simp] theorem insert_apply (i : I) (a : Fin (m i)) (v : S i) :
    insert m S i a v = PiLp.single 2 i (PiLp.single 2 a v) := rfl

omit [Fintype I] in
theorem action_insert (g : G) (i : I) (a : Fin (m i)) (v : S i) :
    action m S rho g (insert m S i a v) = insert m S i a (rho i g v) := by
  ext j b
  by_cases hij : i = j
  · subst j
    by_cases hab : a = b <;> simp [hab]
  · simp [hij]

theorem sum_insert (x : Space m S) : (∑ i, ∑ a, insert m S i a (x i a)) = x := by
  ext j b
  simp only [insert_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

def entry (T : Representation.IntertwiningMap (action m S rho) (action m S rho))
    (i j : I) (a : Fin (m i)) (b : Fin (m j)) :
    Representation.IntertwiningMap (rho j) (rho i) where
  toLinearMap :=
    { toFun := fun v => T (insert m S j b v) i a
      map_add' := by intros; simp only [map_add, PiLp.add_apply]
      map_smul' := by intros; simp only [map_smul, PiLp.smul_apply, RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    have h := T.isIntertwining _ _ g (insert m S j b v)
    rw [action_insert] at h
    exact congrArg (fun x : Space m S => x i a) h

variable (hirred : ∀ i, (rho i).IsIrreducible)
  (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (rho j) (rho i)))
  [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)]

omit [Fintype I] [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)] in
include hirred hne in
theorem entry_off_diagonal
    (T : Representation.IntertwiningMap (action m S rho) (action m S rho))
    (i j : I) (hij : i ≠ j) (a : Fin (m i)) (b : Fin (m j)) :
    entry m S rho T i j a b = 0 := by
  let : (rho i).IsIrreducible := hirred i
  let : (rho j).IsIrreducible := hirred j
  let : IsEmpty (Representation.Equiv (rho j) (rho i)) := hne i j hij
  exact Subsingleton.elim _ _

def coefficients (T : Representation.IntertwiningMap (action m S rho) (action m S rho)) :
    Matrices m := fun i a b => by
  let : (rho i).IsIrreducible := hirred i
  exact (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := rho i)).surjective (entry m S rho T i i a b) |>.choose

omit [Fintype I] [∀ i, Nontrivial (S i)] in
theorem entry_diagonal_apply
    (T : Representation.IntertwiningMap (action m S rho) (action m S rho))
    (i : I) (a b : Fin (m i)) (v : S i) :
    entry m S rho T i i a b v = coefficients m S rho hirred T i a b • v := by
  let : (rho i).IsIrreducible := hirred i
  have h := ((Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := rho i)).surjective (entry m S rho T i i a b)).choose_spec
  exact (congrArg (fun f : Representation.IntertwiningMap (rho i) (rho i) => f v) h).symm

omit [∀ i, Nontrivial (S i)] in
include hne in
theorem apply_eq_mix
    (T : Representation.IntertwiningMap (action m S rho) (action m S rho))
    (x : Space m S) :
    T x = HilbertMultiplicityOperator.mix m S (coefficients m S rho hirred T) x := by
  conv_lhs => rw [← sum_insert m S x, map_sum]
  simp only [map_sum]
  ext i a
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b _
    exact entry_diagonal_apply m S rho hirred T i a b (x i b)
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro b _
    exact congrArg (fun f : Representation.IntertwiningMap (rho j) (rho i) => f (x j b))
      (entry_off_diagonal m S rho hirred hne T i j hji.symm a b)
  · simp

omit [∀ i, Nontrivial (S i)] in
include hirred hne in
theorem operator_exhausts (T : Space m S →L[ℂ] Space m S)
    (hT : ∀ g x, T (action m S rho g x) = action m S rho g (T x)) :
    ∃ A : Matrices m, HilbertMultiplicityOperator.operator m S A = T := by
  let f : Representation.IntertwiningMap (action m S rho) (action m S rho) :=
    { toLinearMap := T.toLinearMap
      isIntertwining' g := LinearMap.ext (hT g) }
  refine ⟨coefficients m S rho hirred f, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact (apply_eq_mix m S rho hirred hne f x).symm

omit [DecidableEq I] [∀ i, Nontrivial (S i)] in
theorem operator_commutes (A : Matrices m) (g : G) (x : Space m S) :
    HilbertMultiplicityOperator.operator m S A (action m S rho g x) =
      action m S rho g (HilbertMultiplicityOperator.operator m S A x) := by
  ext i a
  simp [HilbertMultiplicityOperator.operator_apply, map_sum]

open HilbertMultiplicityOperator (operator operator_mem_unitary_iff operator_injective
  continuous_operator isClosedEmbedding_operator)
open UnitaryCentralizerTransport (unitaryCentralizer)

def unitaryMap : (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) →*
    unitaryCentralizer (action m S rho) where
  toFun A := ⟨⟨operator m S (fun i => A i),
    (operator_mem_unitary_iff m S _).mpr (fun i => (A i).2)⟩, fun g => by
      apply ContinuousLinearMap.ext
      intro x
      exact operator_commutes m S rho (fun i => A i) g x⟩
  map_one' := Subtype.ext (Subtype.ext (operator m S).map_one)
  map_mul' A B := Subtype.ext (Subtype.ext ((operator m S).map_mul
    (fun i => A i) (fun i => B i)))

omit [DecidableEq I] in
theorem unitaryMap_injective : Function.Injective (unitaryMap m S rho) := by
  intro A B h
  have hab := operator_injective m S
    (congrArg (fun u : unitaryCentralizer (action m S rho) => u.val.val) h)
  funext i
  exact Subtype.ext (congrFun hab i)

include hirred hne in
theorem unitaryMap_surjective : Function.Surjective (unitaryMap m S rho) := by
  intro u
  obtain ⟨A, hA⟩ := operator_exhausts m S rho hirred hne u.val.val
    (fun g x => congrArg (fun T : Space m S →L[ℂ] Space m S => T x) (u.2 g).eq)
  have hunit := (operator_mem_unitary_iff m S A).mp (hA.symm ▸ u.val.property)
  exact ⟨fun i => ⟨A i, hunit i⟩, Subtype.ext (Subtype.ext hA)⟩

omit [DecidableEq I] in
theorem continuous_unitaryMap : Continuous (unitaryMap m S rho) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_operator m S).comp
    (continuous_pi fun i => (continuous_apply i).subtype_val)

/-- The full U centralizer, with named factors and no determinant-one restriction. -/
def unitaryEquiv : (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) ≃ₜ*
    unitaryCentralizer (action m S rho) := by
  let e := MulEquiv.ofBijective (unitaryMap m S rho)
    ⟨unitaryMap_injective m S rho, unitaryMap_surjective m S rho hirred hne⟩
  refine { e with
    continuous_toFun := continuous_unitaryMap m S rho
    continuous_invFun := ?_ }
  let coeff : unitaryCentralizer (action m S rho) → Matrices m := fun u i => e.symm u i
  have hc : Continuous coeff := by
    apply (isClosedEmbedding_operator m S).isEmbedding.isInducing.continuous_iff.mpr
    have he : operator m S ∘ coeff =
        (fun u : unitaryCentralizer (action m S rho) => u.val.val) := by
      funext u
      exact congrArg (fun v : unitaryCentralizer (action m S rho) => v.val.val)
        (e.apply_symm_apply u)
    exact (continuous_subtype_val.comp continuous_subtype_val).congr
      (fun u => (congrFun he u).symm)
  exact continuous_pi fun i => ((continuous_apply i).comp hc).subtype_mk _

theorem unitaryEquiv_apply (A : Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) :
    (unitaryEquiv m S rho hirred hne A).val.val = operator m S (fun i => A i) := rfl

theorem unitaryEquiv_symm_action (u : unitaryCentralizer (action m S rho))
    (x : Space m S) (i : I) (a : Fin (m i)) :
    u.val.val x i a = ∑ b, ((unitaryEquiv m S rho hirred hne).symm u i).val a b • x i b := by
  have h := congrArg (fun v : unitaryCentralizer (action m S rho) => v.val.val x i a)
    ((unitaryEquiv m S rho hirred hne).apply_symm_apply u)
  exact h.symm

end

end Math.ExplicitMultiplicity
