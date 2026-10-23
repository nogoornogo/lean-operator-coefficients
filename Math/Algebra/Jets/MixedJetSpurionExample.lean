import Math.Algebra.Jets.MixedJetQuadratic
import Math.RepresentationTheory.Spurions.LocalSpurionEvaluation
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionDegreeExamples
import Mathlib.Algebra.Ring.Int.Units

/-! A sign spurion on the complete (2 odd, 1 even, 2 derivative) mixed IBP
quotient. The action is induced on actual fields before taking the quotient. -/
namespace Math.MixedJetSpurionExample
set_option autoImplicit false
noncomputable section
open Representation PolynomialCovariantEvaluation MixedJetQuadratic
open scoped TensorProduct

@[reducible] local instance : AddCommGroup Ambient := inferInstance
@[reducible] local instance : Module ℂ Ambient := inferInstance
@[reducible] local instance : AddCommGroup Source := inferInstance
@[reducible] local instance : Module ℂ Source := inferInstance
@[reducible] local instance : AddCommGroup Quotient := inferInstance
@[reducible] local instance : Module ℂ Quotient := inferInstance

abbrev Group := ℤˣ
instance groupFintype : Fintype Group :=
  ⟨{1, -1}, fun g => by simpa using Int.units_eq_one_or g⟩

theorem group_card : Fintype.card Group = 2 := by
  change ({1, -1} : Finset Group).card = 2
  decide

def character : Group →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)

@[simp] theorem character_neg_one : character (-1) = -1 := by simp [character]

theorem character_square (g : Group) : character g * character g = 1 := by
  rcases Int.units_eq_one_or g with rfl | rfl <;> simp

def sign {V : Type*} [AddCommGroup V] [Module ℂ V] : Representation ℂ Group V where
  toFun g := character g • LinearMap.id
  map_one' := by ext v; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change character (g * h) • v = character g • (character h • v)
    rw [character.map_mul, mul_smul]

abbrev oddField := trivial ℂ Group (JetLinear.Field Unit)
abbrev evenField := sign (V := JetLinear.Field Unit)

theorem field_jet (g : Group) (k : ℕ) :
    JetLinear.map (evenField g) (Finsupp.single (jetIndex k) 1) =
      character g • Finsupp.single (jetIndex k) 1 := by
  simp [jetIndex, ScalarJetQuadratic.jetIndex, evenField, sign, JetLinear.map_single]

theorem odd_jet (g : Group) (k : ℕ) :
    JetLinear.map (oddField g) (Finsupp.single (jetIndex k) 1) =
      Finsupp.single (jetIndex k) 1 := by
  simp [jetIndex, ScalarJetQuadratic.jetIndex, oddField, JetLinear.map_single]

theorem action_raw (g : Group) (a b c : ℕ) :
    MixedJetAlgebra.action oddField evenField g (raw a b c) = character g • raw a b c := by
  change ExteriorAlgebra.map (JetLinear.map (oddField g)) (psi a * psi b) ⊗ₜ[ℂ]
    JetLinear.polynomialMap (evenField g) (phi c) = _
  simp only [map_mul, psi, ExteriorAlgebra.map_apply_ι, odd_jet]
  change (psi a * psi b) ⊗ₜ[ℂ] JetLinear.polynomialMap (evenField g) (MvPolynomial.X (jetIndex c)) = _
  rw [JetLinear.polynomialMap_X, field_jet, map_smul]
  simp [JetLinear.linearForm, raw, phi, TensorProduct.tmul_smul]

def sourceAction : Representation ℂ Group Source := MixedJetAlgebra.gradeAction oddField evenField 2 1 2

theorem source_sign (g : Group) (p : Source) : sourceAction g p = character g • p := by
  obtain ⟨a, b, rfl⟩ := source_reconstruct p
  have hf : sourceAction g first = character g • first := Subtype.ext (action_raw g 0 1 1)
  have hs : sourceAction g second = character g • second := Subtype.ext (action_raw g 0 2 0)
  simp only [map_add, map_smul, hf, hs, smul_add, smul_comm (character g)]

def quotientAction : Representation ℂ Group Quotient := sourceAction.quotient relations
  (fun g u hu => by
    change sourceAction g u ∈ relations
    rw [source_sign]
    exact relations.smul_mem _ hu)

theorem quotient_sign (g : Group) (u : Quotient) : quotientAction g u = character g • u := by
  obtain ⟨u, rfl⟩ := relations.mkQ_surjective u
  change relations.mkQ (sourceAction g u) = _
  rw [source_sign, map_smul]

def spurion : Representation ℂ Group (Unit → ℂ) := sign

/-- Dual coordinates are supplied by the proved complete quotient, not a premise. -/
def dualCoordinates : Module.Dual ℂ Quotient ≃ₗ[ℂ] (Unit → ℂ) where
  toFun f := fun _ => f (relations.mkQ first)
  invFun c := c () • quotientEquiv.toLinearMap
  left_inv f := by
    apply LinearMap.ext
    intro u
    have he : u = quotientEquiv u • relations.mkQ first := by
      apply quotientEquiv.injective
      simp [quotientEquiv_mk, reduction_first]
    conv_rhs => rw [he]
    simp [mul_comm]
  right_inv c := by ext i; cases i; simp [quotientEquiv_mk, reduction_first]
  map_add' f g := rfl
  map_smul' z f := rfl

theorem dual_sign (g : Group) (c : Unit → ℂ) :
    coordinateAction dualCoordinates quotientAction.dual g c = spurion g c := by
  ext i
  change (dualCoordinates.symm c) (quotientAction g⁻¹ (relations.mkQ first)) = character g * c i
  rw [quotient_sign, map_smul]
  simp [dualCoordinates, quotientEquiv_mk, reduction_first]

def witness : covariants spurion (coordinateAction dualCoordinates quotientAction.dual) :=
  ⟨fun _ => MvPolynomial.X (), by
    intro g s
    rw [dual_sign]
    ext i
    simp [evaluate_apply, spurion, sign]⟩

theorem witness_degree : DegreeLE witness.val 1 := by intro i; simp [witness]

def evaluated (s : Unit → ℂ) := coefficientEvaluation spurion quotientAction dualCoordinates s witness

@[simp] theorem evaluated_first (s : Unit → ℂ) : evaluated s (relations.mkQ first) = s () := by
  change (dualCoordinates.symm (evaluate s witness.val)) (relations.mkQ first) = _
  simp [dualCoordinates, witness, quotientEquiv_mk, reduction_first]

def coefficient (s : Unit → ℂ) : Source →ₗ[ℂ] ℂ := (evaluated s).toLinearMap.comp relations.mkQ

@[simp] theorem coefficient_first (s : Unit → ℂ) : coefficient s first = s () := evaluated_first s

@[simp] theorem coefficient_second (s : Unit → ℂ) : coefficient s second = -s () := by
  change evaluated s (relations.mkQ second) = _
  rw [ibp_identity, map_neg, evaluated_first]

theorem nonzero_value (s : Unit → ℂ) (hs : s () ≠ 0) : evaluated s ≠ 0 := by
  intro hz
  have he := congrArg (fun f => f (relations.mkQ first)) hz
  exact hs ((evaluated_first s).symm.trans he)

theorem stabilizer_nonzero (s : Unit → ℂ) (hs : s () ≠ 0) : stabilizer spurion s = ⊥ := by
  apply Subgroup.ext
  intro g
  rcases Int.units_eq_one_or g with rfl | rfl
  · simp [stabilizer, spurion, sign]
  · have hn : (-1 : Group) ≠ 1 := by decide
    simp only [Subgroup.mem_bot, hn, iff_false]
    intro he
    have he' : -s () = s () := by simpa [spurion, sign] using congrFun he ()
    have hz : s () = 0 := by linear_combination (-1/2 : ℂ) * he'
    exact hs hz

theorem zero_coefficient (f : IntertwiningMap (quotientAction.comp (stabilizer spurion 0).subtype)
    (trivial ℂ (stabilizer spurion 0) ℂ)) : f = 0 := by
  have hm : (-1 : Group) ∈ stabilizer spurion 0 := by change spurion (-1) 0 = 0; exact map_zero _
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have he := congrArg (fun l : Quotient →ₗ[ℂ] ℂ => l u) (f.isIntertwining' ⟨-1, hm⟩)
  change f (quotientAction (-1) u) = f u at he
  rw [quotient_sign, character_neg_one, map_smul, neg_one_smul] at he
  change f u = 0
  linear_combination (-1/2 : ℂ) * he

theorem zero_evaluation (p : covariants spurion (coordinateAction dualCoordinates quotientAction.dual)) :
    evaluate (0 : Unit → ℂ) p.val = 0 := by
  have hz := zero_coefficient (coefficientEvaluation spurion quotientAction dualCoordinates 0 p)
  have he : dualCoordinates.symm (evaluate 0 p.val) = 0 := congrArg IntertwiningMap.toLinearMap hz
  exact dualCoordinates.symm.injective (he.trans dualCoordinates.symm.map_zero.symm)

theorem degree_zero_evaluation
    (p : covariants spurion (coordinateAction dualCoordinates quotientAction.dual))
    (hp : DegreeLE p.val 0) (s : Unit → ℂ) : evaluate s p.val = 0 :=
  (degree_zero_evaluation_eq p.val hp s 0).trans (zero_evaluation p)

theorem degree_one_sharp :
    (∃ p : covariants spurion (coordinateAction dualCoordinates quotientAction.dual),
      DegreeLE p.val 1 ∧ evaluate (fun _ => 1) p.val ≠ 0) ∧
    (∀ p : covariants spurion (coordinateAction dualCoordinates quotientAction.dual),
      DegreeLE p.val 0 → evaluate (fun _ => 1) p.val = 0) := by
  refine ⟨⟨witness, witness_degree, ?_⟩, fun p hp => degree_zero_evaluation p hp _⟩
  intro he
  have hh := congrFun he ()
  norm_num [witness, evaluate_apply] at hh

/-- The full fixed-grade quotient, with the trivial one-direction local group. -/
def productAction : Representation ℂ (Unit × Group) Quotient :=
  quotientAction.comp (MonoidHom.snd Unit Group)

theorem local_trivial (g : Unit) (u : Quotient) :
    LocalSpurionEvaluation.localAction productAction g u = u := by
  change quotientAction 1 u = u
  simp

def localWitness (s : Unit → ℂ) : LocalSpurionEvaluation.Coefficients productAction spurion s :=
  ⟨evaluated s, fun g u => by rw [local_trivial]⟩

theorem local_zero_coefficient (f : LocalSpurionEvaluation.Coefficients productAction spurion 0) :
    f = 0 := Subtype.ext (zero_coefficient f.val)

theorem localWitness_nonzero (s : Unit → ℂ) (hs : s () ≠ 0) : localWitness s ≠ 0 := by
  intro he
  exact nonzero_value s hs (congrArg Subtype.val he)

/-- The common bridge attains all actual coefficients here within degree one. -/
theorem local_degree_one_surjective : Function.Surjective
    (LocalSpurionEvaluation.evaluation productAction spurion (fun _ => 1) 1) := by
  have he : Fintype.card Group - 1 = 1 := by rw [group_card]
  exact Eq.mp (congrArg (fun b : ℕ => Function.Surjective
    (LocalSpurionEvaluation.evaluation productAction spurion (fun _ => (1 : ℂ)) b)) he)
      (LocalSpurionEvaluation.card_evaluation_surjective productAction spurion (fun _ => 1))

theorem bounded_surjective (s : Unit → ℂ) : Function.Surjective
    (boundedCoefficientEvaluation spurion quotientAction dualCoordinates s 1) := by
  have he : Fintype.card Group - 1 = 1 := by rw [group_card]
  exact he ▸ card_boundedCoefficientEvaluation_surjective spurion quotientAction dualCoordinates s

end
end Math.MixedJetSpurionExample
