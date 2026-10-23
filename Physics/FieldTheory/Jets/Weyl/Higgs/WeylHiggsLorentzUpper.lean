import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstTensor
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LL
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LR
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.RL
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.RR

/-! Necessary actual-group Lorentz constraints on all C5 spinor tensors. -/
namespace Physics.WeylHiggsLorentzUpper
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def C (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
    (a e : Fin 2) (i : Fin 4) : ℂ :=
  WeylDirectionInvariant.component (tensor f c d b r) a e i

theorem component_word (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label) (r : Fin 3)
    (a e : Fin 2) (i : Fin 4) : C f c d b r a e i =
      f (word c d b r (Finsupp.single i 1) (Finsupp.single a 1) (Finsupp.single e 1)) := rfl

theorem component_formula (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (c d : Bool) (b : Fin 4 → Label) (r : Fin 3) (a e : Fin 2) (i : Fin 4) :
    C f c d b r a e i = if c then
      if d then 0 else C f c d b r 0 0 0 * WeylDirectionInvariant.kernel e a i
    else if d then C f c d b r 0 0 0 * WeylDirectionInvariant.kernel a e i else 0 := by
  cases c <;> cases d
  · exact WeylDirectionInvariant.LL.components (tensor f false false b r)
      (tensor_invariant f h false false b r) a e i
  · exact WeylDirectionInvariant.LR.components (tensor f false true b r)
      (tensor_invariant f h false true b r) a e i
  · exact WeylDirectionInvariant.RL.components (tensor f true false b r)
      (tensor_invariant f h true false b r) a e i
  · exact WeylDirectionInvariant.RR.components (tensor f true true b r)
      (tensor_invariant f h true true b r) a e i

theorem seed_mem (j : Label) :
    seed j ∈ TwoSidedDifferential.relations D equations :=
  WeylHiggsRelations.paired_relations (TwoSidedDifferential.seed_mem D seeds ⟨j,rfl⟩)

theorem seed_first_value (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label) :
    f (seed (c,0)*psi d 0*evenField (b 0)*rest b) =
      C f c d b 0 0 0 0+C f c d b 0 0 0 3+C f c d b 0 1 0 1+
        (if c then -Complex.I else Complex.I)*C f c d b 0 1 0 2 := by
  cases c <;>
    simp [component_word,word,Math.MixedFirstJetTensor.word,
      Math.MixedFirstJetTensor.directional_single,seed,left,right,
      add_mul,sub_mul,map_add,map_sub,map_smul,smul_eq_mul]
  ring

theorem seed_first_zero (f : A →ₗ[ℂ] ℂ) (hRel : input.relations ≤ f.ker)
    (c d : Bool) (b : Fin 4 → Label) :
    C f c d b 0 0 0 0+C f c d b 0 0 0 3+C f c d b 0 1 0 1+
      (if c then -Complex.I else Complex.I)*C f c d b 0 1 0 2 = 0 := by
  rw [← seed_first_value]
  apply hRel
  apply Submodule.mem_sup_left
  exact TwoSidedDifferential.right_mem D equations (rest b)
    (TwoSidedDifferential.right_mem D equations (evenField (b 0))
      (TwoSidedDifferential.right_mem D equations (psi d 0) (seed_mem (c,0))))

theorem left_first_coordinate_zero (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker)
    (b : Fin 4 → Label) : C f false true b 0 0 0 0 = 0 := by
  have h3 : C f false true b 0 0 0 3 = C f false true b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
  have h1 : C f false true b 0 1 0 1 = C f false true b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
  have h2 : C f false true b 0 1 0 2 = -Complex.I*C f false true b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
    ring
  have hz := seed_first_zero f hRel false true b
  rw [h3,h1,h2] at hz
  linear_combination (norm := (ring_nf; simp [mul_assoc,Complex.I_mul_I])) (1/4 : ℂ)*hz

theorem right_first_coordinate_zero (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker)
    (b : Fin 4 → Label) : C f true false b 0 0 0 0 = 0 := by
  have h3 : C f true false b 0 0 0 3 = C f true false b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
  have h1 : C f true false b 0 1 0 1 = C f true false b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
  have h2 : C f true false b 0 1 0 2 = Complex.I*C f true false b 0 0 0 0 := by
    rw [component_formula f h]
    norm_num [WeylDirectionInvariant.kernel,LorentzDirections.fromPauli]
    ring
  have hz := seed_first_zero f hRel true false b
  rw [h3,h1,h2] at hz
  linear_combination (norm := (ring_nf; simp [mul_assoc,Complex.I_mul_I]; ring)) (1/4 : ℂ)*hz

theorem first_zero (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker)
    (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    C f c d b 0 a e i = 0 := by
  rw [component_formula f h]
  cases c <;> cases d
  · rfl
  · simp only [Bool.false_eq_true,ite_false,ite_true,left_first_coordinate_zero f h hRel,zero_mul]
  · simp only [Bool.false_eq_true,ite_false,ite_true,right_first_coordinate_zero f h hRel,zero_mul]
  · rfl

end
end Physics.WeylHiggsLorentzUpper
