import Math.RepresentationTheory.Jets.DerivativeProhibition
import Math.RepresentationTheory.Jets.DerivativeLiteratureScalar

/-! Nonvacuous scalar tests and actual IBP/free-EOM countercontrols. -/
namespace Math.DerivativeProhibitionControls
set_option autoImplicit false
noncomputable section
open Representation DerivativeProhibition ScalarJetQuadratic

def neutral : DerivativeInterface.Input Unit ℂ where
  action := trivial ℂ Unit ℂ
  relations := ⊥
  stable _ _ hp := hp

def neutralWitness : neutral.Coefficient := ⟨{
  toLinearMap := LinearMap.id
  isIntertwining' _ := rfl }, by intro p hp; exact hp⟩

theorem neutral_allows : Allows neutral := by
  refine ⟨neutralWitness, ?_⟩
  intro hz
  have h := congrArg (fun f : neutral.Coefficient => f.val 1) hz
  exact one_ne_zero h

def scalarAction : Representation ℂ ℂˣ ℂ where
  toFun g := {
    toFun x := (g:ℂ)*x
    map_add' x y := mul_add _ _ _
    map_smul' c x := by simp [smul_eq_mul]; ring }
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by apply LinearMap.ext; intro x; simp [mul_assoc]

def detected : DerivativeInterface.Input ℂˣ ℂ where
  action := scalarAction
  relations := ⊥
  stable g p hp := by change p = 0 at hp; subst p; exact map_zero _

instance : Nontrivial detected.Source := by
  refine ⟨⟨detected.projection 1,0,?_⟩⟩
  intro hz
  have h := (Submodule.Quotient.mk_eq_zero _).mp hz
  change (1:ℂ) = 0 at h
  exact one_ne_zero h

theorem detected_forbids : Forbids detected := by
  apply (ambient_scalar_supported_iff detected (fun g => (g:ℂ)) ?_).mpr
  · intro _
    refine ⟨Units.mk0 (-1) (by norm_num),?_⟩
    norm_num
  · intro g x
    rfl

def offWitness : DerivativeLiteratureScalar.offInput.Coefficient := ⟨{
  toLinearMap := reduction
  isIntertwining' _ := by ext p; rfl }, by
    intro p hp
    change reduction p = 0
    exact (show p ∈ reduction.ker from by rw [reduction_ker]; exact hp)⟩

theorem off_allows : Allows DerivativeLiteratureScalar.offInput := by
  refine ⟨offWitness,?_⟩
  intro hz
  have h := congrArg (fun f : DerivativeLiteratureScalar.offInput.Coefficient => f.val first) hz
  change reduction first = 0 at h
  rw [reduction_first] at h
  exact one_ne_zero h

theorem on_forbids : Forbids DerivativeLiteratureScalar.onInput :=
  DerivativeLiteratureScalar.on_coefficient_zero

theorem neutral_eom_counterexample :
    Allows DerivativeLiteratureScalar.offInput ∧
    Forbids DerivativeLiteratureScalar.onInput ∧ ¬ ∃ _g : Unit, (1:ℂ) ≠ 1 :=
  ⟨off_allows,on_forbids,by simp⟩

def extraEOM : Submodule ℂ Source :=
  (JetEquation.gradeProjection DerivativeLiteratureScalar.freeSymbol 2 2).ker

theorem extra_stable : ∀ g : Unit, extraEOM ≤
    extraEOM.comap (DerivativeLiteratureScalar.offInput.action g) := fun _ _ h => h

def extended := extend DerivativeLiteratureScalar.offInput extraEOM extra_stable

theorem extended_relations_top : extended.relations = ⊤ := by
  change ScalarJetIBP.relations Unit Unit 2 1 ⊔ extraEOM = ⊤
  rw [sup_comm]
  exact DerivativeLiteratureScalar.on_relations_top

theorem extended_forbids : Forbids extended := by
  intro f
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  exact f.property (by rw [extended_relations_top]; trivial)

theorem reverse_monotonicity_fails :
    ¬ (Forbids extended → Forbids DerivativeLiteratureScalar.offInput) := by
  intro h
  obtain ⟨f,hf⟩ := off_allows
  exact hf (h extended_forbids f)

end
end Math.DerivativeProhibitionControls
