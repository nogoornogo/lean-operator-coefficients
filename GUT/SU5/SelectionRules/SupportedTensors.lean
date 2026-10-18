import GUT.SU5.SelectionRules.SupportedFields
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

open Math

/-!
# Ordered internal tensors on actual supported field spaces

The field spaces are ranges of the injective maps into actual SU(5) matter.
Right-handed fields are their contragredients, not additional matter assumed
in the source. The tensors are not Grassmann/Lorentz operators or amplitudes.
-/

set_option autoImplicit false

namespace GUT.SU5.SupportedTensors

noncomputable section

open MatterSource SupportedFields StandardSMGaugeTensor
open StandardSMResidualTensor SplitRepresentationProjection
open FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H] {n : ℕ} {R : OrdinaryAction H n}

section Range

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}

abbrev Field (F : Realization R sigma chi) := LinearMap.range F.embedding

def fieldCoordinates (F : Realization R sigma chi) : Field F ≃ₗ[ℂ] W :=
  (LinearEquiv.ofInjective F.embedding F.injective).symm

def fieldRepresentation (F : Realization R sigma chi) :
    Representation ℂ (GaugeGroup × H) (Field F) :=
  RepresentationConjugation.pullback (fieldCoordinates F) (charged sigma chi)

def fieldEquiv (F : Realization R sigma chi) :
    Representation.Equiv (fieldRepresentation F) (charged sigma chi) :=
  RepresentationConjugation.equiv (fieldCoordinates F) (charged sigma chi)

/-- The transported action really is the restriction of the ambient action. -/
theorem fieldRepresentation_val (F : Realization R sigma chi)
    (g : GaugeGroup × H) (x : Field F) :
    (fieldRepresentation F g x).val =
      (R g.2).val.val (MatterSource.gauge n (StandardModelEmbedding.hom g.1) x.val) := by
  change F.embedding ((chi g.2 : ℂ) • sigma g.1 (fieldCoordinates F x)) = _
  rw [map_smul, ← F.residual, F.gauge]
  have hx : F.embedding (fieldCoordinates F x) = x.val :=
    congrArg Subtype.val ((LinearEquiv.ofInjective F.embedding F.injective).apply_symm_apply x)
  rw [hx]

def fieldSplit (F : Realization R sigma chi) :
    Split (fieldRepresentation F) (charged sigma chi) := Split.ofEquiv (fieldEquiv F)

end Range

section Duality

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {rho : Representation ℂ GaugeGroup V} {sigma : Representation ℂ GaugeGroup W}

def chargedEquiv (e : Representation.Equiv rho sigma) (chi : H →* Circle) :
    Representation.Equiv (charged rho chi) (charged sigma chi) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := by
    ext x
    change e ((chi g.2 : ℂ) • rho g.1 x) = (chi g.2 : ℂ) • sigma g.1 (e x)
    rw [map_smul]
    exact congrArg ((chi g.2 : ℂ) • ·)
      (e.toIntertwiningMap.isIntertwining rho sigma g.1 x)

def chargedDualEquiv (rho : Representation ℂ GaugeGroup V) (chi : H →* Circle) :
    Representation.Equiv (charged rho chi).dual (charged rho.dual chi⁻¹) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    ext phi x
    change phi ((chi g.2⁻¹ : ℂ) • rho g.1⁻¹ x) = (chi⁻¹ g.2 : ℂ) * phi (rho g.1⁻¹ x)
    simp

def rightSplit [Module.IsReflexive ℂ V] {chi : H →* Circle}
    (F : Realization R rho.dual chi) :
    Split (fieldRepresentation F).dual (charged rho chi⁻¹) :=
  (fieldSplit F).dual.trans
    ((Split.ofEquiv (chargedDualEquiv rho.dual chi)).trans
      (Split.ofEquiv (chargedEquiv (bidualEquiv rho).symm chi⁻¹)))

end Duality

variable {k : Charges (ChargeLabel H)}

def qqueAction (S : Support R k) :=
  ((fieldRepresentation S.quark).tprod (fieldRepresentation S.quark)).tprod
    ((fieldRepresentation S.up).dual.tprod (fieldRepresentation S.electron).dual)

def duqlAction (S : Support R k) :=
  ((fieldRepresentation S.down).dual.tprod (fieldRepresentation S.up).dual).tprod
    ((fieldRepresentation S.quark).tprod (fieldRepresentation S.lepton))

def qqueSplit (S : Support R k) : Split (qqueAction S) (StandardSMResidualTensor.qqueRepresentation k) :=
  ((fieldSplit S.quark).tensor (fieldSplit S.quark)).tensor
    ((rightSplit S.up).tensor (rightSplit S.electron))

def duqlSplit (S : Support R k) : Split (duqlAction S) (StandardSMResidualTensor.duqlRepresentation k) :=
  ((rightSplit S.down).tensor (rightSplit S.up)).tensor
    ((fieldSplit S.quark).tensor (fieldSplit S.lepton))

def qqueTensor (S : Support R k) := qque.comp (qqueSplit S).project.toLinearMap
def duqlTensor (S : Support R k) := duql.comp (duqlSplit S).project.toLinearMap

theorem qqueTensor_nonzero (S : Support R k) : qqueTensor S ≠ 0 :=
  (qqueSplit S).pullback_nonzero qque qque_nonzero

theorem duqlTensor_nonzero (S : Support R k) : duqlTensor S ≠ 0 :=
  (duqlSplit S).pullback_nonzero duql duql_nonzero

theorem qqueTensor_invariant (S : Support R k) (hk : SU5OrbitCompatible k) :
    ∀ g x, qqueTensor S (qqueAction S g x) = qqueTensor S x :=
  (qqueSplit S).pullback_invariant qque (invariant_tensors_of_su5OrbitCompatible k hk).2.2.1

theorem duqlTensor_invariant (S : Support R k) (hk : SU5OrbitCompatible k) :
    ∀ g x, duqlTensor S (duqlAction S g x) = duqlTensor S x :=
  (duqlSplit S).pullback_invariant duql (invariant_tensors_of_su5OrbitCompatible k hk).2.2.2

theorem exists_supported_tensors (R : OrdinaryAction H n) (hn : 0 < n) :
    ∃ (k : Charges (ChargeLabel H)) (S : Support R k),
      SU5OrbitCompatible k ∧ qqueTensor S ≠ 0 ∧ duqlTensor S ≠ 0 ∧
      (∀ g x, qqueTensor S (qqueAction S g x) = qqueTensor S x) ∧
      (∀ g x, duqlTensor S (duqlAction S g x) = duqlTensor S x) := by
  obtain ⟨k, ⟨S⟩, hk⟩ := exists_supported_compatible R hn
  exact ⟨k, S, hk, qqueTensor_nonzero S, duqlTensor_nonzero S,
    qqueTensor_invariant S hk, duqlTensor_invariant S hk⟩

end

end GUT.SU5.SupportedTensors
