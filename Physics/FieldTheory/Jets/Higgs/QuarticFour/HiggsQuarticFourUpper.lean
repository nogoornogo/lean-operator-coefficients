import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalComplete
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLorentzUpper
import Math.RepresentationTheory.Relations.SelectedRelationExtension

/-! Injectivity on every admitted coefficient of the actual entire grade. -/
namespace Physics.HiggsQuarticFourUpper
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInput

theorem internal_one (p : A) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs 1 p = p :=
  congrArg (fun L : Module.End ℂ A => L p) (HiggsInternalSymmetry.act HiggsFieldDictionary.higgs).map_one
theorem lorentz_one (p : A) : HiggsLagrangianInput.transport 1 p = p :=
  congrArg (fun L : Module.End ℂ A => L p) HiggsLagrangianInput.action.map_one
theorem internal_only (g : StandardSMGaugeTensor.GaugeGroup) (p : A) :
    HiggsStandardInput.transport (g,1) p =
      HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g p := by
  rw [HiggsStandardInput.factorize,lorentz_one]
theorem lorentz_only (g : LorentzDirections.Group) (p : A) :
    HiggsStandardInput.transport (1,g) p = HiggsLagrangianInput.transport g p := by
  rw [HiggsStandardInput.factorize,internal_one]

theorem whole_grade_zero (f : A →ₗ[ℂ] ℂ)
    (hInv : ∀ g p, p ∈ V → f (HiggsStandardInput.transport g p) = f p)
    (hRel : P.relations ≤ f.ker) (h1 : f q1 = 0) (h2 : f q2 = 0) (h3 : f q3 = 0)
    (p : V) : f p.val = 0 := by
  have hI : ∀ g p, p ∈ V →
      f (HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g p) = f p := by
    intro g p hp
    simpa only [internal_only] using hInv (g,1) p hp
  have hL : ∀ g p, p ∈ V → f (HiggsLagrangianInput.transport g p) = f p := by
    intro g p hp
    simpa only [lorentz_only] using hInv (1,g) p hp
  apply HiggsQuarticFourLorentzUpper.whole_grade_zero f hL hRel ?_ p
  intro a b c d
  simpa only [HiggsQuarticFourTensors.field_eq] using
    HiggsQuarticFourInternalUpper.all_pairs_zero f hI h1 h2 h3 a b c d

theorem selected_zero (F : selected.Coefficient) (hF : evaluate F = 0) : F = 0 := by
  obtain ⟨f,hf,hr⟩ := SelectedRelationExtension.exists_extension P V stable F
  have hi : ∀ g p, p ∈ V → f (HiggsStandardInput.transport g p) = f p := by
    intro g p hp
    change f (P.action g p) = f p
    rw [hf ⟨P.action g p,stable g hp⟩,hf ⟨p,hp⟩]
    exact F.val.isIntertwining _ _ g ⟨p,hp⟩
  have h1 : f q1 = 0 := (hf (representatives 0)).trans (congrFun hF 0)
  have h2 : f q2 = 0 := (hf (representatives 1)).trans (congrFun hF 1)
  have h3 : f q3 = 0 := (hf (representatives 2)).trans (congrFun hF 2)
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  change F.val p = 0
  exact (hf p).symm.trans (whole_grade_zero f hi hr h1 h2 h3 p)

theorem evaluate_injective : Function.Injective evaluate := by
  intro F G h
  apply sub_eq_zero.mp
  apply selected_zero
  rw [map_sub,h,sub_self]

end
end Physics.HiggsQuarticFourUpper
