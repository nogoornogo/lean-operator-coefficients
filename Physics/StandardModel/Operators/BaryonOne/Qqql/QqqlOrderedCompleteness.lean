import Physics.StandardModel.Gauge.Tensors.QqqlGaugeRegroup
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlLocalCompleteness
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Physical ordered qqql coefficients, with hypercharge and all local
gauge/Weyl invariance discharged. Identical-quark exchanges are separate. -/
namespace Physics.QqqlOrderedCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor
open scoped TensorProduct

abbrev PhysicalGroup := GaugeGroup × WeylSpinor.Group

def localProjection : PhysicalGroup →* QqqlLocalCompleteness.LocalGroup where
  toFun g := (g.1.1, g.1.2.1, g.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem localProjection_surjective : Function.Surjective localProjection := by
  rintro ⟨c, w, s⟩
  exact ⟨((c, w, 1), s), rfl⟩

def quarkSpin := external quark WeylSpinor.left
def leptonSpin := external lepton WeylSpinor.left
def localFields := (quarkSpin.tprod quarkSpin).tprod (quarkSpin.tprod leptonSpin)

def associate : Representation.Equiv
    (external QqqlGaugeRegroup.regrouped (FourSameWeylCompleteness.representation false))
    (QqqlLocalCompleteness.representation.comp localProjection) where
  toLinearEquiv := TensorProduct.assoc ℂ _ _ _
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro c
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro s
    rfl

def localRegroup : Representation.Equiv localFields
    (QqqlLocalCompleteness.representation.comp localProjection) :=
  (regroupFour quark quark quark lepton
    WeylSpinor.left WeylSpinor.left WeylSpinor.left WeylSpinor.left).trans
    ((externalEquiv QqqlGaugeRegroup.equiv (Representation.Equiv.refl _)).trans associate)

variable {R Q L : Type*} [Group R] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

abbrev flavor := (q.tprod q).tprod (q.tprod l)
def fields := ((external quarkSpin q).tprod (external quarkSpin q)).tprod
  ((external quarkSpin q).tprod (external leptonSpin l))
abbrev Coefficient := IntertwiningMap (fields q l)
  (Representation.trivial ℂ (PhysicalGroup × R) ℂ)
abbrev Residual := IntertwiningMap (flavor q l) (Representation.trivial ℂ R ℂ)

def projection : PhysicalGroup × R →* QqqlLocalCompleteness.LocalGroup × R :=
  localProjection.prodMap (MonoidHom.id R)

theorem projection_surjective : Function.Surjective (projection (R := R)) := by
  rintro ⟨g, r⟩
  obtain ⟨h, hh⟩ := localProjection_surjective g
  exact ⟨(h, r), Prod.ext hh rfl⟩

def regroup : Representation.Equiv (fields q l)
    (external (QqqlLocalCompleteness.representation.comp localProjection) (flavor q l)) :=
  (regroupFour quarkSpin quarkSpin quarkSpin leptonSpin q q q l).trans
    (externalEquiv localRegroup (Representation.Equiv.refl _))

def descend : Representation.Equiv
    (external (QqqlLocalCompleteness.representation.comp localProjection) (flavor q l))
    ((external QqqlLocalCompleteness.representation (flavor q l)).comp
      (projection (R := R))) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    rfl

/-- No local invariance hypotheses remain on the four residual coordinates. -/
def homEquiv : Coefficient q l ≃ₗ[ℂ] (Fin 2 × Fin 2 → Residual q l) :=
  (InvariantCoefficientTransport.alongEquiv (regroup q l)).trans
    ((InvariantCoefficientTransport.alongEquiv (descend q l)).trans
      ((InvariantCoefficientTransport.alongSurjection _ (projection (R := R))
        projection_surjective).trans (QqqlLocalCompleteness.homEquiv q l)))

theorem assemble_apply (k : Fin 2 × Fin 2 → Residual q l)
    (a b c : SMEpsilonTensor.Color) (v0 v1 v2 v3 : SMEpsilonTensor.Weak)
    (s0 s1 s2 s3 : WeylSpinor.Space) (x y z : Q) (h : L) :
    (homEquiv q l).symm k
      (((((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ]
          ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h))) =
      SMEpsilonTensor.eps3 a b c * FourDoubletProductExchange.evaluate
        (fun i j => k (i,j) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)))
        v0 v1 v2 v3 s0 s1 s2 s3 := by
  change FiniteInvariantFactor.assemble QqqlLocalCompleteness.representation
    (flavor q l) QqqlLocalCompleteness.pairing k
      ((((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ]
        (((v0 ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] (v2 ⊗ₜ[ℂ] v3)) ⊗ₜ[ℂ]
          ((s0 ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] (s2 ⊗ₜ[ℂ] s3)))) ⊗ₜ[ℂ]
          ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))) = _
  trans ∑ ij, QqqlLocalCompleteness.pairing ij
    (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ]
      (((v0 ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] (v2 ⊗ₜ[ℂ] v3)) ⊗ₜ[ℂ]
        ((s0 ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] (s2 ⊗ₜ[ℂ] s3)))) *
      k ij ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
  · exact FiniteInvariantFactor.assemble_apply _ _ _ _ _ _
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, QqqlLocalCompleteness.pairing,
    QqqlLocalCompleteness.colorPairing, FourWeakWeylCompleteness.pairing,
    FourWeakWeylCompleteness.weakPairing, coefficient,
    FourSameWeylCompleteness.basisPairing, FourSameWeylCompleteness.pairing,
    FourDoubletInvariant.tensorPairing_apply, SMEpsilonTensor.colorTensor_tmul,
    FourDoubletProductExchange.evaluate]
  ring

end
end Physics.QqqlOrderedCompleteness
