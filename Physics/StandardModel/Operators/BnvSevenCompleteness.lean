import Physics.StandardModel.Operators.BnvSixResidualCompleteness
import Physics.StandardModel.Operators.BnvSevenSignedCoordinates
import Physics.StandardModel.Operators.BnvSevenDegreeDecomposition

/-! Complete residual-Hom classification of the independently defined
derivative-free matter/Higgs BNV input through dimension seven. -/
namespace GUT.BnvSevenCompleteness
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput BnvMixedInput

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

abbrev ResidualProduct := BnvSixResidualCompleteness.ResidualProduct flavor ×
  (∀ i : Fin 8, BnvSevenSignedCoordinates.Factor flavor scalarFlavor i)

def equiv : bounded flavor scalarFlavor 7 ≃ₗ[ℂ] ResidualProduct flavor scalarFlavor :=
  (BnvSevenDegreeDecomposition.equiv flavor scalarFlavor).trans
    (LinearEquiv.prodCongr
      ((BnvZeroBosonBridge.equiv flavor scalarFlavor).trans
        (BnvSixResidualCompleteness.equiv flavor))
      (BnvSevenSignedCoordinates.equiv flavor scalarFlavor))

def extract := (equiv flavor scalarFlavor).toLinearMap
def reconstruct := (equiv flavor scalarFlavor).symm.toLinearMap

@[simp] theorem reconstruct_extract (f : bounded flavor scalarFlavor 7) :
    reconstruct flavor scalarFlavor (extract flavor scalarFlavor f) = f :=
  (equiv flavor scalarFlavor).symm_apply_apply f

@[simp] theorem extract_reconstruct (q : ResidualProduct flavor scalarFlavor) :
    extract flavor scalarFlavor (reconstruct flavor scalarFlavor q) = q :=
  (equiv flavor scalarFlavor).apply_symm_apply q

theorem forbidden_iff : (∀ f : bounded flavor scalarFlavor 7, f = 0) ↔
    (∀ q : BnvSixResidualCompleteness.ResidualProduct flavor, q = 0) ∧
      (∀ i, ∀ q : BnvSevenSignedCoordinates.Factor flavor scalarFlavor i, q = 0) := by
  constructor
  · intro h
    have hz (q : ResidualProduct flavor scalarFlavor) : q = 0 :=
      (equiv flavor scalarFlavor).symm.injective
        ((h ((equiv flavor scalarFlavor).symm q)).trans
          (equiv flavor scalarFlavor).symm.map_zero.symm)
    constructor
    · intro q
      exact congrArg Prod.fst (hz (q,0))
    · intro i q
      have hh := congrArg Prod.snd (hz (0,Pi.single i q))
      simpa using congrFun hh i
  · rintro ⟨hs,hh⟩ f
    have hz : equiv flavor scalarFlavor f = 0 :=
      Prod.ext (hs _) (funext (fun i => hh i _))
    exact (equiv flavor scalarFlavor).injective
      (hz.trans (equiv flavor scalarFlavor).map_zero.symm)

theorem nonzero_iff : (∃ f : bounded flavor scalarFlavor 7, f ≠ 0) ↔
    (∃ q : BnvSixResidualCompleteness.ResidualProduct flavor, q ≠ 0) ∨
      (∃ i, ∃ q : BnvSevenSignedCoordinates.Factor flavor scalarFlavor i, q ≠ 0) := by
  simpa only [not_and_or, not_forall, not_not] using
    not_congr (forbidden_iff flavor scalarFlavor)

end
end GUT.BnvSevenCompleteness
