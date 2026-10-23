import Physics.FieldTheory.Jets.Weyl.Equations.ConjugateWeylEquation
import Math.Algebra.Jets.JetExteriorAdjoint

/-! A paired left/right on-shell Weyl source with derivative-compatible adjoint.
IBP is a vector-space quotient, not an algebra quotient. -/
namespace Physics.WeylJetAdjoint
set_option autoImplicit false
noncomputable section
open Math WeylLinearEquation ConjugateWeylEquation

abbrev Paired := Generator × RightGenerator
abbrev Algebra := ExteriorAlgebra ℂ Paired

def conjugation : Paired →ₛₗ[starRingEnd ℂ] Paired where
  toFun x := (toLeft x.2, toRight x.1)
  map_add' x y := by simp
  map_smul' c x := by simp [map_smulₛₗ]

theorem conjugation_involutive (x : Paired) : conjugation (conjugation x) = x := by
  change (toLeft (toRight x.1), toRight (toLeft x.2)) = x
  simp

def shift (i : Fin 4) : Paired →ₗ[ℂ] Paired :=
  (LinearJetEquation.shift seed i).prodMap (LinearJetEquation.shift rightSeed i)

theorem conjugation_shift (i : Fin 4) (x : Paired) : conjugation (shift i x) = shift i (conjugation x) :=
  Prod.ext (toLeft_shift i x.2) (toRight_shift i x.1)

theorem shift_commute (i j : Fin 4) : (shift i).comp (shift j) = (shift j).comp (shift i) := by
  apply LinearMap.ext
  intro x
  exact Prod.ext (LinearMap.congr_fun (LinearJetEquation.shift_commute seed i j) x.1)
    (LinearMap.congr_fun (LinearJetEquation.shift_commute rightSeed i j) x.2)

def action : Representation ℂ Group Paired := WeylLinearEquation.action.prod rightAction

theorem conjugation_action (g : Group) (x : Paired) : conjugation (action g x) = action g (conjugation x) :=
  Prod.ext (toLeft_action g x.2) (toRight_action g x.1)

def adjoint : Algebra →ₛₗ[starRingEnd ℂ] Algebra := JetExteriorAdjoint.map conjugation

theorem adjoint_generator (v : Paired) : adjoint (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (conjugation v) :=
  JetExteriorAdjoint.map_generator conjugation v

theorem adjoint_mul (x y : Algebra) : adjoint (x * y) = adjoint y * adjoint x :=
  JetExteriorAdjoint.map_mul conjugation x y

theorem adjoint_involutive (x : Algebra) : adjoint (adjoint x) = x :=
  JetExteriorAdjoint.involutive conjugation conjugation_involutive x

def derivative (i : Fin 4) : Algebra →ₗ[ℂ] Algebra := ExteriorAlgebra.derivationOfLinear (shift i)

theorem adjoint_derivative (i : Fin 4) (x : Algebra) : adjoint (derivative i x) = derivative i (adjoint x) :=
  JetExteriorAdjoint.derivative conjugation shift conjugation_shift i x

theorem derivative_commute (i j : Fin 4) (x : Algebra) : derivative i (derivative j x) = derivative j (derivative i x) :=
  ExteriorAlgebra.derivationOfLinear_comm_apply (shift_commute i j) x

theorem adjoint_action (g : Group) (x : Algebra) :
    ExteriorAlgebra.map (action g) (adjoint x) = adjoint (ExteriorAlgebra.map (action g) x) :=
  JetExteriorAdjoint.naturality conjugation conjugation (action g)
    (fun v => (conjugation_action g v).symm) x

abbrev IBP := JetExteriorAdjoint.relations shift
abbrev Source := Algebra ⧸ IBP

theorem adjoint_ibp {x : Algebra} (hx : x ∈ IBP) : adjoint x ∈ IBP :=
  JetExteriorAdjoint.stable conjugation shift conjugation_shift hx

def sourceAdjoint : Source →ₛₗ[starRingEnd ℂ] Source :=
  JetExteriorAdjoint.quotient conjugation shift conjugation_shift

@[simp] theorem sourceAdjoint_mk (x : Algebra) : sourceAdjoint (IBP.mkQ x) = IBP.mkQ (adjoint x) := rfl

theorem sourceAdjoint_involutive (x : Source) : sourceAdjoint (sourceAdjoint x) = x :=
  JetExteriorAdjoint.quotient_involutive conjugation shift conjugation_shift conjugation_involutive x

def rawConjugation : (Jets × Jets) →ₛₗ[starRingEnd ℂ] (Jets × Jets) where
  toFun x := (JetConjugation.coefficients x.2, JetConjugation.coefficients x.1)
  map_add' x y := by simp
  map_smul' c x := by simp [map_smulₛₗ]

def projection : (Jets × Jets) →ₗ[ℂ] Paired := relations.mkQ.prodMap rightRelations.mkQ

theorem projection_surjective : Function.Surjective projection := by
  rintro ⟨x, y⟩
  obtain ⟨v, rfl⟩ := relations.mkQ_surjective x
  obtain ⟨w, rfl⟩ := rightRelations.mkQ_surjective y
  exact ⟨(v, w), rfl⟩

theorem projection_conjugation (v : Jets × Jets) :
    projection (rawConjugation v) = conjugation (projection v) := rfl

def algebraProjection : ExteriorAlgebra ℂ (Jets × Jets) →ₐ[ℂ] Algebra := ExteriorAlgebra.map projection

theorem algebraProjection_surjective : Function.Surjective algebraProjection :=
  ExteriorAlgebra.map_surjective_iff.mpr projection_surjective

theorem algebraProjection_adjoint (x : ExteriorAlgebra ℂ (Jets × Jets)) :
    algebraProjection (JetExteriorAdjoint.map rawConjugation x) = adjoint (algebraProjection x) :=
  JetExteriorAdjoint.naturality rawConjugation conjugation projection projection_conjugation x

theorem left_descendant_zero (p : JetDirections.Symbols (Fin 4)) (f : Equations) :
    algebraProjection (ExteriorAlgebra.ι ℂ (LinearJetEquation.multiple p (seed f), 0)) = 0 := by
  rw [algebraProjection, ExteriorAlgebra.map_apply_ι]
  change ExteriorAlgebra.ι ℂ (relations.mkQ (LinearJetEquation.multiple p (seed f)), rightRelations.mkQ 0) = 0
  rw [descendant_zero, map_zero]
  exact map_zero _

theorem right_descendant_zero (p : JetDirections.Symbols (Fin 4)) (f : Equations) :
    algebraProjection (ExteriorAlgebra.ι ℂ (0, LinearJetEquation.multiple p (rightSeed f))) = 0 := by
  rw [algebraProjection, ExteriorAlgebra.map_apply_ι]
  change ExteriorAlgebra.ι ℂ (relations.mkQ 0, rightRelations.mkQ (LinearJetEquation.multiple p (rightSeed f))) = 0
  rw [map_zero, show rightRelations.mkQ (LinearJetEquation.multiple p (rightSeed f)) = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearJetEquation.descendant_mem rightSeed p f)]
  exact map_zero _

end
end Physics.WeylJetAdjoint
