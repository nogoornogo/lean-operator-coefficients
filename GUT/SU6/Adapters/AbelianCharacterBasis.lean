import GUT.SU6.SelectionRules.Models.AbelianActualSpectrum
import Mathlib.LinearAlgebra.DirectSum.Basis

open Physics

open Math

/-!
# Prescribed eigenbases from Abelian trace characters

An actual unitary Abelian representation whose trace is a prescribed finite
sum of scalar characters has an eigenbasis with exactly those labels,
including repeated labels. Fiber cardinalities are proved by faithful
character evaluation; no representation equivalence is assumed.
-/

set_option autoImplicit false

namespace GUT.AbelianCharacterBasis

noncomputable section

open UnitaryVirtualRealization AbelianActualSpectrum

variable {G : Type*} [CommGroup G]

local instance : DecidableEq (G →* ℂ) := Classical.decEq _

abbrev BasisIndex (R : ActualUnitaryGroupRepresentation G) :=
  Σ i : SectorIndex R, Fin (Module.finrank ℂ (sector R i))

def sectorBasis (R : ActualUnitaryGroupRepresentation G) (i : SectorIndex R) :
    Module.Basis (Fin (Module.finrank ℂ (sector R i))) ℂ (sector R i) :=
  Module.finBasis ℂ (sector R i)

theorem internal (R : ActualUnitaryGroupRepresentation G) : DirectSum.IsInternal (sector R) :=
  (action R).indexedCharacterSubmodule_isInternal (decomposition R)

def basis (R : ActualUnitaryGroupRepresentation G) : Module.Basis (BasisIndex R) ℂ R.V :=
  (internal R).collectedBasis (sectorBasis R)

def label (R : ActualUnitaryGroupRepresentation G) (i : BasisIndex R) : G →* ℂ :=
  character R i.1

theorem basis_action (R : ActualUnitaryGroupRepresentation G) (g : G) (i : BasisIndex R) :
    R.rho g (basis R i) = label R i g • basis R i := by
  have hm : basis R i ∈ sector R i.1 :=
    (internal R).collectedBasis_mem (sectorBasis R) i
  exact sector_action R i.1 ⟨basis R i, hm⟩ g

theorem character_sum (R : ActualUnitaryGroupRepresentation G) (g : G) :
    R.rho.character g = ∑ i : BasisIndex R, label R i g :=
  WeightTheory.trace_eq_sum_of_basis_eigen (basis R) (R.rho g) _ (basis_action R g)

def labelPolynomial {I : Type*} [Fintype I] (chi : I → G →* ℂ) : Polynomial G :=
  ∑ i, Finsupp.single (chi i) 1

theorem eval_labelPolynomial {I : Type*} [Fintype I] (chi : I → G →* ℂ) (g : G) :
    eval (labelPolynomial chi) g = ∑ i, chi i g := by
  classical
  unfold eval labelPolynomial
  rw [← Finsupp.sum_finsetSum_index]
  · simp
  · simp
  · intros; simp [add_mul]

theorem labelPolynomial_apply {I : Type*} [Fintype I]
    (chi : I → G →* ℂ) (psi : G →* ℂ) :
    labelPolynomial chi psi = (Fintype.card {i // chi i = psi} : ℤ) := by
  classical
  simp [labelPolynomial, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.sum_boole]

variable {I : Type*} [Fintype I]

theorem label_fiber_card (R : ActualUnitaryGroupRepresentation G) (chi : I → G →* ℂ)
    (ht : ∀ g, R.rho.character g = ∑ i, chi i g) (psi : G →* ℂ) :
    Fintype.card {j : BasisIndex R // label R j = psi} =
      Fintype.card {i : I // chi i = psi} := by
  have he : labelPolynomial (label R) = labelPolynomial chi :=
    eval_injective _ _ (fun g => by
      rw [eval_labelPolynomial, eval_labelPolynomial, ← character_sum, ht])
  have h := congrArg (fun p => p psi) he
  simp only [labelPolynomial_apply] at h
  exact_mod_cast h

def matching (R : ActualUnitaryGroupRepresentation G) (chi : I → G →* ℂ)
    (ht : ∀ g, R.rho.character g = ∑ i, chi i g) : I ≃ BasisIndex R := by
  classical
  exact Equiv.ofFiberEquiv fun psi => Fintype.equivOfCardEq (label_fiber_card R chi ht psi).symm

theorem matching_label (R : ActualUnitaryGroupRepresentation G) (chi : I → G →* ℂ)
    (ht : ∀ g, R.rho.character g = ∑ i, chi i g) (i : I) :
    label R (matching R chi ht i) = chi i := by
  classical
  exact Equiv.ofFiberEquiv_map _ i

def prescribedBasis (R : ActualUnitaryGroupRepresentation G) (chi : I → G →* ℂ)
    (ht : ∀ g, R.rho.character g = ∑ i, chi i g) : Module.Basis I ℂ R.V :=
  (basis R).reindex (matching R chi ht).symm

theorem prescribedBasis_action (R : ActualUnitaryGroupRepresentation G) (chi : I → G →* ℂ)
    (ht : ∀ g, R.rho.character g = ∑ i, chi i g) (g : G) (i : I) :
    R.rho g (prescribedBasis R chi ht i) = chi i g • prescribedBasis R chi ht i := by
  simp only [prescribedBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  rw [basis_action, matching_label]

end

end GUT.AbelianCharacterBasis
