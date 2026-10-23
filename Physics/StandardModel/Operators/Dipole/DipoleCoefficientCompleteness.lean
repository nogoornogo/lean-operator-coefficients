import Physics.StandardModel.Operators.Dipole.DipoleLocalSector
import Math.RepresentationTheory.Invariants.InvariantEvaluation

open Math

/-! Completeness of ordered dipole sectors with arbitrary residual lepton
multiplicities and one residual-trivial Higgs. No coefficient-generation map
or dynamics is assumed. -/
namespace Physics.DipoleCoefficientCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor InvariantCoefficientTransport
open scoped TensorProduct

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

def lepton := external DipoleLocalSector.lepton a
def electron := external DipoleLocalSector.electron b.dual
def higgs := external DipoleLocalSector.higgs (Representation.trivial ℂ H ℂ)
def strengthB := external DipoleLocalSector.strengthB (Representation.trivial ℂ H ℂ)
def strengthW := external DipoleLocalSector.strengthW (Representation.trivial ℂ H ℂ)

def orderedB := ((lepton a).tprod (electron b)).tprod (higgs.tprod strengthB)
def orderedW := ((lepton a).tprod (electron b)).tprod (higgs.tprod strengthW)

/-- All invariant ordered four-species coefficients, specified before assembly. -/
abbrev SectorB := Invariants (orderedB a b)
abbrev SectorW := Invariants (orderedW a b)

def residualRegroup : Representation.Equiv
    ((a.tprod b.dual).tprod ((Representation.trivial ℂ H ℂ).tprod
      (Representation.trivial ℂ H ℂ))) (a.tprod b.dual) :=
  (tensorEquiv (Representation.Equiv.refl _)
    (Representation.TensorProduct.lid ℂ (Representation.trivial ℂ H ℂ))).trans
    (Representation.TensorProduct.rid ℂ (a.tprod b.dual))

def regroupB : Representation.Equiv (orderedB a b)
    (external DipoleLocalSector.factoredB (a.tprod b.dual)) :=
  (regroupFour _ _ _ _ a b.dual (Representation.trivial ℂ H ℂ)
    (Representation.trivial ℂ H ℂ)).trans
    (externalEquiv DipoleLocalSector.regroupB (residualRegroup a b))

def regroupW : Representation.Equiv (orderedW a b)
    (external DipoleLocalSector.factoredW (a.tprod b.dual)) :=
  (regroupFour _ _ _ _ a b.dual (Representation.trivial ℂ H ℂ)
    (Representation.trivial ℂ H ℂ)).trans
    (externalEquiv DipoleLocalSector.regroupW (residualRegroup a b))

variable [FiniteDimensional ℂ B]

def equivB : SectorB a b ≃ₗ[ℂ] IntertwiningMap a b :=
  (alongEquiv (regroupB a b)).trans
    ((NormalizedInvariantFactor.equiv _ _ DipoleLocalSector.contractionB
      DipoleLocalSector.witnessB DipoleLocalSector.normalizedB DipoleLocalSector.uniqueB).trans
      (InvariantEvaluation.equiv a b))

def equivW : SectorW a b ≃ₗ[ℂ] IntertwiningMap a b :=
  (alongEquiv (regroupW a b)).trans
    ((NormalizedInvariantFactor.equiv _ _ DipoleLocalSector.contractionW
      DipoleLocalSector.witnessW DipoleLocalSector.normalizedW DipoleLocalSector.uniqueW).trans
      (InvariantEvaluation.equiv a b))

def equiv : (SectorB a b × SectorW a b) ≃ₗ[ℂ]
    (IntertwiningMap a b × IntertwiningMap a b) :=
  LinearEquiv.prodCongr (equivB a b) (equivW a b)

theorem exists_nonzero_iff :
    (∃ c : SectorB a b × SectorW a b, c ≠ 0) ↔
      ∃ k : IntertwiningMap a b, k ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hn
    have hk : ∀ k : IntertwiningMap a b, k = 0 := by simpa using hn
    apply hc
    apply (equiv a b).injective
    simpa only [map_zero] using
      (Prod.ext (hk ((equiv a b c).1)) (hk ((equiv a b c).2)))
  · rintro ⟨k, hk⟩
    refine ⟨(equiv a b).symm (k, 0), ?_⟩
    intro h
    have he := congrArg (equiv a b) h
    simp only [LinearEquiv.apply_symm_apply, map_zero] at he
    exact hk (congrArg Prod.fst he)

end
end Physics.DipoleCoefficientCompleteness
