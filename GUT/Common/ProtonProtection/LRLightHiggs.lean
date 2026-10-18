import GUT.PatiSalam.Embeddings.PhiRepresentation
import GUT.Common.ProtonProtection.BLResidualRestriction
import Math.RepresentationTheory.Decomposition.RepresentationConjugation
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! One explicitly selected LR bidoublet column. The quadratic selection is
an SM-stage hypothesis, not a derived LR scalar potential. -/
namespace GUT.LRLightHiggs
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor
open PatiSalam.StandardModelEmbedding PatiSalam.ComponentRepresentations
abbrev LRGroup := Matrix.specialUnitaryGroup (Fin 2) ℂ ×
  Matrix.specialUnitaryGroup (Fin 2) ℂ × Circle
abbrev Phi := PatiSalam.PhiRepresentation.Phi
abbrev Two := PatiSalam.ComponentRepresentations.Two

def forgetX : LRGroup →* PSGroup where
  toFun g := (1,g.1,g.2.1)
  map_one' := rfl
  map_mul' _ _ := by simp

def bidoublet : Representation ℂ LRGroup Phi :=
  PatiSalam.PhiRepresentation.representation.comp forgetX

def smEmbedding : GaugeGroup →* LRGroup where
  toFun g := (g.2.1,rightHom g,g.2.2)
  map_one' := by simp
  map_mul' _ _ := by simp

def residualEmbedding : BLResidualRestriction.Residual →* LRGroup where
  toFun g := (1,1,BLResidualRestriction.embedding g)
  map_one' := by simp
  map_mul' _ _ := by simp

theorem restriction_eq : bidoublet.comp smEmbedding =
    PatiSalam.PhiRepresentation.representation.comp hom := by
  ext g f x i
  simp [bidoublet,forgetX,smEmbedding,PatiSalam.PhiRepresentation.representation,
    Representation.linHom_apply,left,right,hom]

theorem residual_neutral (g : BLResidualRestriction.Residual) :
    bidoublet (residualEmbedding g) = 1 := by
  ext f x i
  simp [bidoublet,forgetX,residualEmbedding,PatiSalam.PhiRepresentation.representation,
    Representation.linHom_apply,left,right]

def includeHiggs : Two →ₗ[ℂ] Phi :=
  PatiSalam.PhiRepresentation.joinMap.comp (LinearMap.inr ℂ Two Two)

def projectHiggs : Phi →ₗ[ℂ] Two :=
  (LinearMap.snd ℂ Two Two).comp PatiSalam.PhiRepresentation.equiv.symm.toLinearMap

@[simp] theorem project_include (x : Two) : projectHiggs (includeHiggs x) = x := by
  change (PatiSalam.PhiRepresentation.split (PatiSalam.PhiRepresentation.join (0,x))).2 = x
  rw [PatiSalam.PhiRepresentation.split_join]

theorem include_injective : Function.Injective includeHiggs := by
  intro x y he
  simpa using congrArg projectHiggs he

/-- The domain is exactly the existing positive-hypercharge SM Higgs. -/
theorem include_equivariant (g : GaugeGroup) (x : Two) :
    bidoublet (smEmbedding g) (includeHiggs x) =
      includeHiggs (BnvMixedInput.scalarGauge 0 g x) := by
  have he : bidoublet (smEmbedding g) = PatiSalam.PhiRepresentation.representation (hom g) :=
    congrArg (fun r : Representation ℂ GaugeGroup Phi => r g) restriction_eq
  rw [he]
  change PatiSalam.PhiRepresentation.representation (hom g)
    (PatiSalam.PhiRepresentation.join (0,x)) =
      PatiSalam.PhiRepresentation.join (0,twist weak 3 g x)
  rw [PatiSalam.PhiRepresentation.join_equivariant]
  congr 1
  change ((twist weak (-3)) g 0, (twist weak 3) g x) = _
  simp

/-- Quadratic operator in the exact (-3,+3) column coordinates. -/
def quadratic (heavy light : ℂ) : Phi →ₗ[ℂ] Phi :=
  PatiSalam.PhiRepresentation.equiv.toLinearMap.comp
    (((heavy • LinearMap.id : Two →ₗ[ℂ] Two).prodMap
      (light • LinearMap.id : Two →ₗ[ℂ] Two)).comp
        PatiSalam.PhiRepresentation.equiv.symm.toLinearMap)

@[simp] theorem split_quadratic (heavy light : ℂ) (f : Phi) :
    PatiSalam.PhiRepresentation.split (quadratic heavy light f) =
      (heavy • (PatiSalam.PhiRepresentation.split f).1,
       light • (PatiSalam.PhiRepresentation.split f).2) := by
  change PatiSalam.PhiRepresentation.split (PatiSalam.PhiRepresentation.join _) = _
  rw [PatiSalam.PhiRepresentation.split_join]
  rfl

theorem quadratic_equivariant (heavy light : ℂ) (g : GaugeGroup) (f : Phi) :
    quadratic heavy light (bidoublet (smEmbedding g) f) =
      bidoublet (smEmbedding g) (quadratic heavy light f) := by
  have he : bidoublet (smEmbedding g) = PatiSalam.PhiRepresentation.representation (hom g) :=
    congrArg (fun r : Representation ℂ GaugeGroup Phi => r g) restriction_eq
  rw [he]
  apply PatiSalam.PhiRepresentation.equiv.symm.injective
  change PatiSalam.PhiRepresentation.split (quadratic heavy light _) =
    PatiSalam.PhiRepresentation.split (PatiSalam.PhiRepresentation.representation (hom g) _)
  rw [split_quadratic,PatiSalam.PhiRepresentation.split_equivariant,
    PatiSalam.PhiRepresentation.split_equivariant,split_quadratic]
  change (heavy • ((twist weak (-3)) g _),light • ((twist weak 3) g _)) =
    ((twist weak (-3)) g (heavy • _),(twist weak 3) g (light • _))
  simp

/-- A zero positive eigenvalue and a nonzero negative one select just one doublet. -/
theorem kernel_eq_range (heavy : ℂ) (hh : heavy ≠ 0) :
    LinearMap.ker (quadratic heavy 0) = LinearMap.range includeHiggs := by
  ext f
  constructor
  · intro hf
    have hs := congrArg PatiSalam.PhiRepresentation.split hf
    change PatiSalam.PhiRepresentation.split (quadratic heavy 0 f) = _ at hs
    rw [split_quadratic] at hs
    have hfirst : (PatiSalam.PhiRepresentation.split f).1 = 0 := by
      have he : heavy • (PatiSalam.PhiRepresentation.split f).1 = 0 := congrArg Prod.fst hs
      exact (smul_eq_zero.mp he).resolve_left hh
    refine ⟨projectHiggs f,?_⟩
    change PatiSalam.PhiRepresentation.join (0,(PatiSalam.PhiRepresentation.split f).2) = f
    rw [← hfirst]
    exact PatiSalam.PhiRepresentation.join_split f
  · rintro ⟨x,rfl⟩
    apply PatiSalam.PhiRepresentation.equiv.symm.injective
    change PatiSalam.PhiRepresentation.split (quadratic heavy 0 (includeHiggs x)) = _
    rw [split_quadratic]
    change (heavy • (PatiSalam.PhiRepresentation.split (PatiSalam.PhiRepresentation.join (0,x))).1,
      (0 : ℂ) • (PatiSalam.PhiRepresentation.split (PatiSalam.PhiRepresentation.join (0,x))).2) = _
    rw [PatiSalam.PhiRepresentation.split_join]
    simp

/-- A supplied quadratic operator with these column eigenvalues has exactly
one light doublet; the coordinate premise is not proved for a UV potential. -/
theorem kernel_of_coordinates (M : Phi →ₗ[ℂ] Phi) (heavy : ℂ) (hh : heavy ≠ 0)
    (hM : ∀ f, PatiSalam.PhiRepresentation.split (M f) =
      (heavy • (PatiSalam.PhiRepresentation.split f).1,0)) :
    LinearMap.ker M = LinearMap.range includeHiggs := by
  have he : M = quadratic heavy 0 := by
    apply LinearMap.ext
    intro f
    apply PatiSalam.PhiRepresentation.equiv.symm.injective
    change PatiSalam.PhiRepresentation.split (M f) =
      PatiSalam.PhiRepresentation.split (quadratic heavy 0 f)
    rw [hM,split_quadratic]
    simp
  rw [he]
  exact kernel_eq_range heavy hh

/-- A positive real heavy eigenvalue is a permitted special case. -/
theorem positive_heavy_kernel (heavy : ℝ) (hh : 0 < heavy) :
    LinearMap.ker (quadratic (heavy : ℂ) 0) = LinearMap.range includeHiggs :=
  kernel_eq_range _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hh))

/-- The complete kernel, not merely one invariant line inside it. -/
def lightEquiv (heavy : ℂ) (hh : heavy ≠ 0) :
    Two ≃ₗ[ℂ] LinearMap.ker (quadratic heavy 0) where
  toFun x := ⟨includeHiggs x, by
    rw [kernel_eq_range heavy hh]
    exact ⟨x,rfl⟩⟩
  invFun x := projectHiggs x.val
  map_add' x y := by apply Subtype.ext; exact map_add includeHiggs x y
  map_smul' c x := by apply Subtype.ext; exact map_smul includeHiggs c x
  left_inv := project_include
  right_inv x := by
    apply Subtype.ext
    have hle : LinearMap.ker (quadratic heavy 0) ≤ LinearMap.range includeHiggs :=
      le_of_eq (kernel_eq_range heavy hh)
    obtain ⟨y,hy⟩ := hle x.property
    change includeHiggs (projectHiggs x.val) = x.val
    rw [← hy,project_include]

def lightRepresentation (heavy : ℂ) (hh : heavy ≠ 0) :
    Representation ℂ GaugeGroup (LinearMap.ker (quadratic heavy 0)) :=
  RepresentationConjugation.pullback (lightEquiv heavy hh).symm (BnvMixedInput.scalarGauge 0)

def lightRepresentationEquiv (heavy : ℂ) (hh : heavy ≠ 0) :
    Representation.Equiv (lightRepresentation heavy hh) (BnvMixedInput.scalarGauge 0) :=
  RepresentationConjugation.equiv (lightEquiv heavy hh).symm (BnvMixedInput.scalarGauge 0)

/-- The scalar dual is the existing negative-Higgs species, with no new conjugation convention. -/
def dualLightRepresentationEquiv (heavy : ℂ) (hh : heavy ≠ 0) :
    Representation.Equiv (lightRepresentation heavy hh).dual (BnvMixedInput.scalarGauge 1) :=
  SplitRepresentationProjection.dualEquiv (lightRepresentationEquiv heavy hh)

theorem light_action (heavy : ℂ) (hh : heavy ≠ 0) (g : GaugeGroup)
    (x : LinearMap.ker (quadratic heavy 0)) :
    (lightRepresentation heavy hh g x).val = bidoublet (smEmbedding g) x.val := by
  change includeHiggs (BnvMixedInput.scalarGauge 0 g (projectHiggs x.val)) = _
  rw [← include_equivariant]
  have hi := congrArg Subtype.val ((lightEquiv heavy hh).apply_symm_apply x)
  change includeHiggs (projectHiggs x.val) = x.val at hi
  rw [hi]

/-- Restricting the actual LR residual action to the light kernel is neutral. -/
theorem light_residual_action (g : BLResidualRestriction.Residual)
    (heavy : ℂ) (x : LinearMap.ker (quadratic heavy 0)) :
    bidoublet (residualEmbedding g) x.val = x.val := by
  rw [residual_neutral]
  rfl

end
end GUT.LRLightHiggs
