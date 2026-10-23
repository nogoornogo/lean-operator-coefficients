import Physics.StandardModel.Operators.Weinberg.WeinbergSMInterface
import Physics.StandardModel.Operators.Weinberg.LiWeinbergConvention
import Math.RepresentationTheory.Invariants.InvariantFunctionalCoordinates
import TauCeti.LinearAlgebra.SymmetricPower.Basis
import Mathlib.Data.Sym.Card

open Math

/-! Normalized local interpretation of Li v2, page 38, Out[7]. -/
namespace Physics.LiWeinbergCertificate
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SMEpsilonTensor LiWeinbergConvention
open scoped TensorProduct
variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

abbrev Residual := TensorSquareMultilinear.symmetricIntertwiners a
  (Representation.trivial ℂ R ℂ)

/-- Assemble the invariant local factor and the supplied symmetric flavor map,
before physical-field descent. This is not defined using the sector inverse. -/
def ordered (k : Residual a) : WeinbergResidualHom.sector a :=
  ⟨coefficient WeinbergResidualHom.localContraction k.val, by
    intro x y h s t u v
    change WeinbergResidualHom.localContraction _ * k.val (v ⊗ₜ[ℂ] u) =
      -(WeinbergResidualHom.localContraction _ * k.val (u ⊗ₜ[ℂ] v))
    rw [k.property u v]
    change (WeinbergWeakInvariant.contraction _ * eps2 t s) * k.val _ =
      -((WeinbergWeakInvariant.contraction _ * eps2 s t) * k.val _)
    rw [WeinbergWeakInvariant.contraction_apply, WeinbergWeakInvariant.contraction_apply]
    simp only [eps2]
    ring⟩

def candidate (k : Residual a) : WeinbergSMInterface.ModelSector a :=
  (WeinbergSMInterface.reducedEquiv a).symm
    ((WeinbergModelSector.sectorEquiv a).symm (ordered a k))

theorem ordered_eq (k : Residual a) :
    ordered a k = (WeinbergResidualHom.symmetricEquiv a).symm k := rfl

theorem candidate_eq (k : Residual a) : candidate a k =
    (WeinbergSMInterface.homEquiv a).symm
      (TensorSquareMultilinear.symmetricSquareEquiv a _ k) := by
  simp only [WeinbergSMInterface.homEquiv, WeinbergModelSector.homEquiv_agrees,
    WeinbergResidualHom.homEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem extract_candidate (k : Residual a) :
    WeinbergSMInterface.homEquiv a (candidate a k) =
      TensorSquareMultilinear.symmetricSquareEquiv a _ k := by
  rw [candidate_eq, LinearEquiv.apply_symm_apply]

theorem candidate_extract (f : WeinbergSMInterface.ModelSector a) :
    candidate a ((TensorSquareMultilinear.symmetricSquareEquiv a _).symm
      (WeinbergSMInterface.homEquiv a f)) = f := by
  rw [candidate_eq, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem candidate_apply (k : Residual a) (x y : Weak) (s t : WeylSpinor.Space)
    (u v : F) (h : Fin 2 → Weak) :
    candidate a k (exteriorPower.ιMulti ℂ 2
      ![(x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u, (y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v] ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ h) = polarizedLocal x y h s t * k.val (u ⊗ₜ[ℂ] v) := by
  rw [← WeinbergSMInterface.coefficientEquiv_apply]
  change ((WeinbergModelSector.sectorEquiv a)
    ((WeinbergModelSector.sectorEquiv a).symm (ordered a k))).val
      (WeinbergResidualHom.input x y h s t u v) = _
  rw [LinearEquiv.apply_symm_apply]
  change (WeinbergWeakInvariant.contraction _ * eps2 s t) * k.val _ = _
  rw [WeinbergWeakInvariant.contraction_apply]
  rfl

theorem candidate_diagonal (k : Residual a) (x y h : Weak)
    (s t : WeylSpinor.Space) (u v : F) :
    candidate a k (exteriorPower.ιMulti ℂ 2
      ![(x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] u, (y ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] v] ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ ![h,h]) = paperLocal x y h s t * k.val (u ⊗ₜ[ℂ] v) := by
  rw [candidate_apply, diagonal_local]

theorem probe (k : Residual a) (u v : F) :
    candidate a k (exteriorPower.ιMulti ℂ 2
      ![(weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] u,
        (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] v] ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ ![weakBasis 1,weakBasis 1]) = k.val (u ⊗ₜ[ℂ] v) := by
  rw [candidate_diagonal]
  norm_num [paperLocal, eps2, weakBasis]

theorem mass_formula (k : Residual a) (v : ℂ) (u w : F) :
    (WeinbergSMInterface.mass a v (candidate a k)).form u w =
      v ^ 2 * k.val (u ⊗ₜ[ℂ] w) := by
  rw [← WeinbergSMInterface.mass_evaluation, candidate_diagonal]
  simp [paperLocal, WeinbergMajorana.vacuum, eps2, weakBasis, pow_two]

variable {I : Type*} [Fintype I] [DecidableEq I] (b : Module.Basis I ℂ F)

def finiteEquiv := (WeinbergSMInterface.homEquiv a).trans
  (InvariantFunctionalCoordinates.equiv (a.symmetricPower 2) (b.symmetricPower 2))

def flavorEquiv (hr : ∀ g, (a.symmetricPower 2) g = 1) :
    WeinbergSMInterface.ModelSector a ≃ₗ[ℂ] (Sym I 2 → ℂ) :=
  (WeinbergSMInterface.homEquiv a).trans
    (InvariantFunctionalCoordinates.unrestrictedEquiv _ (b.symmetricPower 2) hr)

def flavorBasis (hr : ∀ g, (a.symmetricPower 2) g = 1) :=
  Module.Basis.ofEquivFun (flavorEquiv a b hr)

omit [DecidableEq I] in
theorem flavorBasis_independent (hr : ∀ g, (a.symmetricPower 2) g = 1) :
    LinearIndependent ℂ (flavorBasis a b hr) := (flavorBasis a b hr).linearIndependent

omit [DecidableEq I] in
theorem flavorBasis_spans (hr : ∀ g, (a.symmetricPower 2) g = 1) :
    Submodule.span ℂ (Set.range (flavorBasis a b hr)) = ⊤ := (flavorBasis a b hr).span_eq

include b in
theorem flavor_finrank (hr : ∀ g, (a.symmetricPower 2) g = 1) :
    Module.finrank ℂ (WeinbergSMInterface.ModelSector a) =
      Fintype.card I * (Fintype.card I + 1) / 2 := by
  rw [(flavorEquiv a b hr).finrank_eq, Module.finrank_pi]
  rw [Sym.card_sym_eq_choose, Nat.choose_two_right]
  simp [Nat.mul_comm]

omit [Fintype I] [DecidableEq I] in
theorem finite_inverse_is_candidate
    (c : InvariantFunctionalCoordinates.space (a.symmetricPower 2) (b.symmetricPower 2)) :
    (finiteEquiv a b).symm c = candidate a
      ((TensorSquareMultilinear.symmetricSquareEquiv a _).symm
        ((InvariantFunctionalCoordinates.equiv _ (b.symmetricPower 2)).symm c)) := by
  rw [candidate_eq, LinearEquiv.apply_symm_apply]
  rfl

omit [Fintype I] [DecidableEq I] in
theorem flavor_entry (hr : ∀ g, (a.symmetricPower 2) g = 1)
    (f : WeinbergSMInterface.ModelSector a) (i j : I) :
    flavorEquiv a b hr f (TauCeti.Sym.ofFn ![i,j]) =
      (WeinbergSMInterface.homEquiv a f)
        (SymmetricPower.tprod ℂ ![b i,b j]) := by
  change ((b.symmetricPower 2).constr ℂ).symm
    (WeinbergSMInterface.homEquiv a f).toLinearMap (TauCeti.Sym.ofFn ![i,j]) = _
  rw [Module.Basis.constr_symm_apply, Module.Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn]
  rfl

theorem trivial_symmetric_action (g : R) :
    ((Representation.trivial ℂ R F).symmetricPower 2) g = 1 := by
  apply SymmetricSquareDescent.ext
  intro v
  rw [Representation.symmetricPower_apply_tprod]
  rfl

theorem finite_trivial_finrank (n : ℕ) :
    Module.finrank ℂ (WeinbergSMInterface.ModelSector
      (Representation.trivial ℂ R (Fin n → ℂ))) = n * (n + 1) / 2 := by
  simpa using flavor_finrank (Representation.trivial ℂ R (Fin n → ℂ))
    (Pi.basisFun ℂ (Fin n)) (trivial_symmetric_action (F := Fin n → ℂ))

omit [DecidableEq I] in
theorem flavorBasis_is_candidate (hr : ∀ g, (a.symmetricPower 2) g = 1) (i : Sym I 2) :
    candidate a ((TensorSquareMultilinear.symmetricSquareEquiv a _).symm
      (WeinbergSMInterface.homEquiv a (flavorBasis a b hr i))) = flavorBasis a b hr i :=
  candidate_extract a _

theorem sign_candidate_nonzero : ∃ k : Residual WeylMassTwoTorsion.signRepresentation,
    candidate WeylMassTwoTorsion.signRepresentation k ≠ 0 := by
  let k := WeinbergScalarFlavor.scalarCoefficient WeylMassTwoTorsion.signRepresentation
    (by
      intro r
      obtain rfl | rfl := Int.units_eq_one_or r <;>
        norm_num [WeylMassTwoTorsion.signRepresentation_apply])
  refine ⟨k, ?_⟩
  intro hz
  have hp := probe WeylMassTwoTorsion.signRepresentation k 1 1
  rw [hz] at hp
  change (0 : ℂ) = 1 * 1 at hp
  norm_num at hp

section ActualFields
variable {L H : Type*} [AddCommGroup L] [Module ℂ L] [AddCommGroup H] [Module ℂ H]
  (l : Representation ℂ (WeinbergSMInterface.PhysicalGroup R) L)
  (h : Representation ℂ (WeinbergSMInterface.PhysicalGroup R) H)

def onFieldsCandidate (i : WeinbergSMInterface.Inputs a l h) (k : Residual a) :=
  (WeinbergSMInterface.onFieldsModelEquiv a l h i).symm (candidate a k)

theorem onFields_extract (i : WeinbergSMInterface.Inputs a l h) (k : Residual a) :
    WeinbergSMInterface.onFieldsEquiv a l h i (onFieldsCandidate a l h i k) =
      TensorSquareMultilinear.symmetricSquareEquiv a _ k := by
  change WeinbergSMInterface.homEquiv a
    ((WeinbergSMInterface.onFieldsModelEquiv a l h i)
      ((WeinbergSMInterface.onFieldsModelEquiv a l h i).symm (candidate a k))) = _
  rw [LinearEquiv.apply_symm_apply, extract_candidate]

theorem onFields_reconstruct (i : WeinbergSMInterface.Inputs a l h)
    (f : WeinbergSMInterface.Sector l h) :
    onFieldsCandidate a l h i
      ((TensorSquareMultilinear.symmetricSquareEquiv a _).symm
        (WeinbergSMInterface.onFieldsEquiv a l h i f)) = f := by
  unfold onFieldsCandidate WeinbergSMInterface.onFieldsEquiv
  rw [LinearEquiv.trans_apply, candidate_extract, LinearEquiv.symm_apply_apply]
end ActualFields

end
end Physics.LiWeinbergCertificate
