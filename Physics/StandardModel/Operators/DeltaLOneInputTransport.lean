import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Math.RepresentationTheory.SpeciesCoefficientTransport

open Math

/-! Species-preserving actual-field identifications transport the independent
degree sector, before applying the four-family residual classification. -/
namespace GUT.DeltaLOneInputTransport
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput
variable {G : Type*} [Group G] {V W : Species → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  {a : ∀ s, Representation ℂ G (V s)} {b : ∀ s, Representation ℂ G (W s)}
  (e : ∀ s, Representation.Equiv (a s) (b s))

def fieldsEquiv : Representation.Equiv (FiniteSpeciesExterior.representation a)
    (FiniteSpeciesExterior.representation b) :=
  SpeciesCoefficientTransport.fieldsEquiv a b e

@[simp] theorem fieldsEquiv_single (s : Species) (x : V s) :
    fieldsEquiv e (Pi.single s x) = Pi.single s (e s x) := by
  exact SpeciesCoefficientTransport.fieldsEquiv_single a b e s x

def pull (f : FiniteSpeciesExterior.Coefficient b 4) :
    FiniteSpeciesExterior.Coefficient a 4 :=
  f.comp ((fieldsEquiv e).exteriorPower 4).toIntertwiningMap

theorem pull_mem (degree : ℤ) (f : sector b degree) : pull e f.val ∈ sector a degree := by
  intro labels hn
  ext v
  change f.val (((fieldsEquiv e).exteriorPower 4)
    (exteriorPower.ιMulti ℂ 4 (fun i => Pi.single (labels i) (v i)))) = 0
  rw [Representation.Equiv.exteriorPower_apply_ιMulti]
  change f.val (exteriorPower.ιMulti ℂ 4
    (fun i => fieldsEquiv e (Pi.single (labels i) (v i)))) = 0
  simp only [fieldsEquiv_single]
  have he := congrArg (fun k => k (fun i => e (labels i) (v i))) (f.property labels hn)
  exact he

theorem pull_symm (f : FiniteSpeciesExterior.Coefficient a 4) :
    pull e (pull (fun s => (e s).symm) f) = f := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change f (((fieldsEquiv (fun s => (e s).symm)).exteriorPower 4)
    (((fieldsEquiv e).exteriorPower 4) (exteriorPower.ιMulti ℂ 4 v))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti,
    Representation.Equiv.exteriorPower_apply_ιMulti]
  apply congrArg f
  apply congrArg (exteriorPower.ιMulti ℂ 4)
  funext i s
  exact (e s).toLinearEquiv.symm_apply_apply (v i s)

def equiv (degree : ℤ) : sector b degree ≃ₗ[ℂ] sector a degree :=
  (SpeciesCoefficientTransport.equiv a b e 4
    (fun labels => DeltaLOneSpeciesSupport.leptonDegree (counts labels) = degree)).symm

/-- The common species transport retains the former extraction and inverse,
including the support condition on all ten signed species. -/
@[simp] theorem equiv_apply (degree : ℤ) (f : sector b degree) :
    (equiv e degree f).val = pull e f.val := rfl

@[simp] theorem equiv_symm_apply (degree : ℤ) (f : sector a degree) :
    ((equiv e degree).symm f).val = pull (fun s => (e s).symm) f.val := rfl

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  {A : Species → Type*} [∀ s, AddCommGroup (A s)] [∀ s, Module ℂ (A s)]
  (actual : ∀ s, Representation ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × R) (A s))
  (identifications : ∀ s, Representation.Equiv (actual s) (DeltaLOneSignedFields.field flavor s))

/-- The model supplies actual gauge/Weyl/residual field identifications;
completeness does not infer them from charges or UV naming conventions. -/
def onFieldsEquiv : sector actual 1 ≃ₗ[ℂ]
    DeltaLOneCoefficientCompleteness.ResidualProduct flavor :=
  (equiv identifications 1).symm.trans (DeltaLOneCoefficientCompleteness.equiv flavor)

end
end GUT.DeltaLOneInputTransport
