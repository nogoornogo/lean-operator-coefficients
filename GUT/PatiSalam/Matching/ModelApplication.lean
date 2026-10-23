import GUT.PatiSalam.Matching.LightFields
import GUT.PatiSalam.Matching.CoefficientParameters
import GUT.PatiSalam.Matching.UVComponent

open Physics

/-! Conditional one-generation PS coefficient application, with explicit UV,
mass, VEV and chirality conventions. No canonically normalized finite-mu
matching, amplitude, decay rate or ultraviolet generation of C_X is proved. -/
namespace GUT.PatiSalam.ModelApplication
noncomputable section
open Math GUT SMEpsilonTensor
open scoped TensorProduct
open CoefficientParameters

structure Parameters where
  CL : ℂ
  CR : ℂ
  v : ℂ
  Lambda : ℂ
  y : ℂ
  Y : ℂ
  M : ℂ
  m : ℂ
  w : ℂ

def kL (p : Parameters) := covariant p.CL p.v p.Lambda p.y p.Y p.M p.m
def kR (p : Parameters) := covariant p.CR p.v p.Lambda p.y p.Y p.M p.m

/-- The identical-Q weak contraction has a half relative to the resolved u,d seed. -/
def smCoefficient (p : Parameters) :=
  (kL p / 2) • TypedVertex.assembled 1 + kR p • TypedVertex.assembled 0

theorem admitted (p : Parameters) : smCoefficient p ∈
    BnvMixedInput.bnvSector TypedVertex.flavor TypedVertex.scalarFlavor 4 1 :=
  (BnvMixedInput.bnvSector _ _ 4 1).add_mem
    ((BnvMixedInput.bnvSector _ _ 4 1).smul_mem _ (TypedVertex.admitted 1))
    ((BnvMixedInput.bnvSector _ _ 4 1).smul_mem _ (TypedVertex.admitted 0))

/-- Substitution and actual light-component pullback, rather than just a prefactor. -/
def lightCoefficient (p : Parameters) := MixedSingleBosonEvaluation.pull
  (smCoefficient p).toLinearMap
  (Pi.single (1 : BnvMixedInput.ScalarSpecies) (p.w • TypedVertex.neutralHiggs))
  LightFields.injection

theorem light_eq (p : Parameters) : lightCoefficient p =
    LightFields.combined (kL p / 2) (kR p) p.w := by
  unfold lightCoefficient smCoefficient LightFields.combined LightFields.leftCoefficient
  rw [Representation.IntertwiningMap.add_toLinearMap,
    Representation.IntertwiningMap.toLinearMap_smul, Representation.IntertwiningMap.toLinearMap_smul,
    MixedSingleBosonEvaluation.pull_add, MixedSingleBosonEvaluation.pull_smul,
    MixedSingleBosonEvaluation.pull_smul]

theorem rr_value (p : Parameters) : lightCoefficient p LightFields.rrProbe = -(kR p*p.w/2) := by
  rw [light_eq, LightFields.combined_rr]

theorem lr_value (p : Parameters) : lightCoefficient p LightFields.lrProbe = -(kL p*p.w/2) := by
  rw [light_eq, LightFields.combined_lr]
  ring

/-- Exact zero/nonzero conditions on the admitted symbolic parameter domain. -/
theorem light_nonzero_iff (p : Parameters)
    (hLambda : p.Lambda ≠ 0) (hm : p.m ≠ 0) (hM : p.M ≠ 0) :
    lightCoefficient p ≠ 0 ↔ p.w ≠ 0 ∧ p.v ≠ 0 ∧ p.y ≠ 0 ∧ p.Y ≠ 0 ∧
      (p.CL ≠ 0 ∨ p.CR ≠ 0) := by
  rw [light_eq, LightFields.combined_nonzero_iff]
  have hL := covariant_nonzero_iff p.CL p.v p.Lambda p.y p.Y p.M p.m hLambda hm hM
  have hR := covariant_nonzero_iff p.CR p.v p.Lambda p.y p.Y p.M p.m hLambda hm hM
  simp only [kL, kR, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
  tauto

theorem exact_light_mass (p : Parameters) (hM : p.M ≠ 0) :
    (NeutralMass.mass (p.Y*star p.w) p.M 0).mulVec
      (NeutralMass.mode (p.Y*star p.w) p.M) = 0 :=
  NeutralMass.exact_zero_mode _ _ hM

/-- Both paths agree with the barred coordinate of the exact unnormalized mass chart. -/
theorem mass_projection_matching (p : Parameters) :
    kL p*p.w = generated p.CL p.v p.Lambda p.y
      (barProjection (p.Y*star p.w) p.M) p.m ∧
    kR p*p.w = generated p.CR p.v p.Lambda p.y
      (barProjection (p.Y*star p.w) p.M) p.m :=
  ⟨covariant_after_vev _ _ _ _ _ _ _ _, covariant_after_vev _ _ _ _ _ _ _ _⟩

/-- Resolving the QQ weak components before counting the UV quarter would double count. -/
theorem left_uv_quarter (C v Lambda : ℂ) :
    C/(4*Lambda)*(-2*v) = -(diquark C v Lambda/2) := by
  unfold diquark
  ring

/-- Selected source contraction: the physical scalar mass term is -m,
while the PS d,u color order contributes -J in our u,d ordering. -/
theorem source_elimination (C v Lambda y Y M m : ℂ) (hm : m ≠ 0) (J K : ℂ) :
    Math.TwoSourceQuadraticElimination.action (LinearMap.mul ℂ ℂ) (-m)
      (diquark C v Lambda) (-y*(-star Y/star M)) (-J) K
      (Math.TwoSourceQuadraticElimination.leftSolution (-m) (diquark C v Lambda) (-J))
      (Math.TwoSourceQuadraticElimination.rightSolution (-m) (-y*(-star Y/star M)) K) =
      covariant C v Lambda y Y M m * (J*K) :=
  eliminated_oriented_pair (LinearMap.mul ℂ ℂ) _ _ _ _ _ _ hm J K

/-- The eliminated RR current is the typed invariant seed on arbitrary pure fields. -/
theorem rr_current_matching (C v Lambda y Y M m : ℂ) (hm : m ≠ 0)
    (a b c : Color) (l h : Weak) (s t u z : WeylSpinor.Space) :
    Math.TwoSourceQuadraticElimination.action (LinearMap.mul ℂ ℂ) (-m)
      (diquark C v Lambda) (-y*(-star Y/star M))
      (-(eps3 a b c * eps2 s t)) (eps2 l h * eps2 u z)
      (Math.TwoSourceQuadraticElimination.leftSolution (-m) (diquark C v Lambda)
        (-(eps3 a b c * eps2 s t)))
      (Math.TwoSourceQuadraticElimination.rightSolution (-m) (-y*(-star Y/star M))
        (eps2 l h * eps2 u z)) =
      covariant C v Lambda y Y M m *
        TypedVertex.ordered 0 (TypedVertex.rrInputs a b c l s t u z) (TypedVertex.higgsInput h) := by
  rw [source_elimination _ _ _ _ _ _ _ hm, TypedVertex.rr_ordered]
  ring

/-- QQ retains its two weak components; the UV coefficient is C/2 in this seed. -/
theorem lr_current_matching (C v Lambda y Y M m : ℂ) (hm : m ≠ 0)
    (a b c : Color) (x z l h : Weak) (s t u q : WeylSpinor.Space) :
    Math.TwoSourceQuadraticElimination.action (LinearMap.mul ℂ ℂ) (-m)
      (diquark (C/2) v Lambda) (-y*(-star Y/star M))
      (-(eps3 a b c * eps2 x z * eps2 s t)) (eps2 l h * eps2 u q)
      (Math.TwoSourceQuadraticElimination.leftSolution (-m) (diquark (C/2) v Lambda)
        (-(eps3 a b c * eps2 x z * eps2 s t)))
      (Math.TwoSourceQuadraticElimination.rightSolution (-m) (-y*(-star Y/star M))
        (eps2 l h * eps2 u q)) =
      (covariant C v Lambda y Y M m/2) *
        TypedVertex.ordered 1 (TypedVertex.lrInputs a b c x z l s t u q) (TypedVertex.higgsInput h) := by
  rw [source_elimination _ _ _ _ _ _ _ hm, TypedVertex.lr_ordered]
  simp only [covariant_formula]
  ring

/-- A real, nonzero exact point, satisfying M=y*star v as well as mu=0. -/
def control : Parameters := ⟨1,1,1,1,1,1,1,1,1⟩

theorem control_mass_relation : control.M = control.y*star control.v := by norm_num [control]
theorem control_nonzero : lightCoefficient control ≠ 0 := by
  rw [light_nonzero_iff control (by norm_num [control]) (by norm_num [control])
    (by norm_num [control])]
  norm_num [control]

theorem zero_uv (p : Parameters) (hL : p.CL = 0) (hR : p.CR = 0) : lightCoefficient p = 0 := by
  rw [light_eq]
  simp [LightFields.combined, kL, kR, covariant, generated_formula, hL, hR]

/-- Formula-level comparison only: p=-s is a supplied barred mixing coordinate.
No equality with the paper's approximate/canonically normalized s is assumed here. -/
theorem paper_prefactor (C vR Lambda y s m : ℂ) :
    generated C (vR/(Real.sqrt 2 : ℂ)) Lambda y (-s) m =
      -(C*y*vR*s/((Real.sqrt 2 : ℂ)*Lambda*m)) := by
  rw [generated_formula]
  ring
end
end GUT.PatiSalam.ModelApplication
