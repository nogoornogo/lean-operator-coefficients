import Math.RepresentationTheory.Weights.CyclicWeightCoordinates
import Math.RepresentationTheory.Symmetric.SymmetricTensorFunctional
import Physics.StandardModel.Operators.Weinberg.LiWeinbergCertificate
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlCertificate
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueCertificate
import Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalExteriorCompleteness

open Math

namespace Physics.FlavoredCyclicCoordinates
set_option autoImplicit false
noncomputable section
open Representation CyclicWeightCoordinates SelectionCriteria
open scoped TensorProduct
variable {N : ℕ} [NeZero N]
universe u
variable {I J K L : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

def fourBasis := ((Pi.basisFun ℂ I).tensorProduct (Pi.basisFun ℂ J)).tensorProduct
  ((Pi.basisFun ℂ K).tensorProduct (Pi.basisFun ℂ L))
def fourCharge (a : I → ZMod N) (b : J → ZMod N) (c : K → ZMod N) (d : L → ZMod N)
    (i : (I × J) × (K × L)) := (a i.1.1+b i.1.2)+(c i.2.1+d i.2.2)

theorem four_weights (a : I → ZMod N) (b : J → ZMod N)
    (c : K → ZMod N) (d : L → ZMod N) :
    IsWeightBasis (((diagonal a).tprod (diagonal b)).tprod
      ((diagonal c).tprod (diagonal d))) fourBasis (fourCharge a b c d) := by
  intro g ij
  rcases ij with ⟨⟨i,j⟩,⟨k,h⟩⟩
  simp only [fourBasis, Module.Basis.tensorProduct_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, diagonal_basis, TensorProduct.smul_tmul_smul]
  simp only [fourCharge, add_mul, AddChar.map_add_eq_mul]

def duqlEquiv (d : I → ZMod N) (u : J → ZMod N) (q : K → ZMod N) (l : L → ZMod N) :=
  (DuqlExteriorCompleteness.homEquiv (diagonal d) (diagonal u) (diagonal q) (diagonal l)).trans
    (invariantEquiv _ fourBasis (fourCharge d u q l) (four_weights d u q l))

theorem duql_finrank (d : I → ZMod N) (u : J → ZMod N) (q : K → ZMod N) (l : L → ZMod N) :
    Module.finrank ℂ (DuqlExteriorCompleteness.Sector
      (diagonal d) (diagonal u) (diagonal q) (diagonal l)) =
      Fintype.card {i // fourCharge d u q l i=0} := by
  rw [(duqlEquiv d u q l).finrank_eq]; simp

theorem duql_allowed (d : I → ZMod N) (u : J → ZMod N) (q : K → ZMod N) (l : L → ZMod N) :
    Allowed (DuqlExteriorCompleteness.Sector (diagonal d) (diagonal u) (diagonal q) (diagonal l)) ↔
      ∃ i, fourCharge d u q l i=0 := by
  rw [allowed_equiv (DuqlExteriorCompleteness.homEquiv _ _ _ _)]
  exact CyclicWeightCoordinates.allowed_iff _ _ _ (four_weights d u q l)

def duueEquiv (u : I → ZMod N) (d : J → ZMod N) (e : K → ZMod N) :=
  (DuueResidualCompleteness.homEquiv (diagonal u) (diagonal d) (diagonal e)).trans
    (invariantEquiv _ fourBasis (fourCharge u u d e) (four_weights u u d e))

theorem duue_finrank (u : I → ZMod N) (d : J → ZMod N) (e : K → ZMod N) :
    Module.finrank ℂ (DuueExchange.Sector (diagonal u) (diagonal d) (diagonal e)) =
      Fintype.card {i // fourCharge u u d e i=0} := by
  rw [(duueEquiv u d e).finrank_eq]; simp

theorem duue_allowed (u : I → ZMod N) (d : J → ZMod N) (e : K → ZMod N) :
    Allowed (DuueExchange.Sector (diagonal u) (diagonal d) (diagonal e)) ↔
      ∃ i, fourCharge u u d e i=0 := by
  rw [allowed_equiv (DuueResidualCompleteness.homEquiv _ _ _)]
  exact CyclicWeightCoordinates.allowed_iff _ _ _ (four_weights u u d e)

def llhhEquiv (l : I → ZMod N) :=
  (WeinbergSMInterface.homEquiv (diagonal l)).trans
    (invariantEquiv _ ((Pi.basisFun ℂ I).symmetricPower 2) (symmetricCharge 2 l)
      (symmetric_weights _ _ _ 2 (diagonal_weights l)))

theorem llhh_finrank (l : I → ZMod N) :
    Module.finrank ℂ (WeinbergSMInterface.ModelSector (diagonal l)) =
      Fintype.card {s // symmetricCharge 2 l s=0} := by
  rw [(llhhEquiv l).finrank_eq]; simp

theorem llhh_allowed (l : I → ZMod N) :
    Allowed (WeinbergSMInterface.ModelSector (diagonal l)) ↔
      ∃ s, symmetricCharge 2 l s=0 := by
  rw [allowed_equiv (WeinbergSMInterface.homEquiv _)]
  exact CyclicWeightCoordinates.allowed_iff _ _ _
    (symmetric_weights _ _ _ 2 (diagonal_weights l))

def qqueSymmetricEquiv (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :
    QquePhysicalExteriorCompleteness.residualSpace (diagonal q) (diagonal u) (diagonal e) ≃ₗ[ℂ]
      SymmetricTensorFunctional.symmetric (diagonal q) ((diagonal u).tprod (diagonal e)) where
  toFun f := ⟨f.val, by
    intro x y z
    have he : f.val.toLinearMap.comp (TensorProduct.mk ℂ _ _ (y ⊗ₜ[ℂ] x)) =
        f.val.toLinearMap.comp (TensorProduct.mk ℂ _ _ (x ⊗ₜ[ℂ] y)) := by
      apply TensorProduct.ext'; intro a b; exact f.property x y a b
    exact DFunLike.congr_fun he z⟩
  invFun f := ⟨f.val, by intro x y a b; exact f.property x y (a ⊗ₜ[ℂ] b)⟩
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' z f := rfl

def qqueBasis := ((Pi.basisFun ℂ I).symmetricPower 2).tensorProduct
  ((Pi.basisFun ℂ J).tensorProduct (Pi.basisFun ℂ K))
def qqueCharge (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N)
    (i : Sym I 2 × (J × K)) := symmetricCharge 2 q i.1 + (u i.2.1+e i.2.2)

theorem qque_weights (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :
    IsWeightBasis (((diagonal q).symmetricPower 2).tprod
      ((diagonal u).tprod (diagonal e))) qqueBasis (qqueCharge q u e) := by
  intro g ij
  rcases ij with ⟨s,⟨i,j⟩⟩
  simp only [qqueBasis, Module.Basis.tensorProduct_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, symmetric_weights (diagonal q) (Pi.basisFun ℂ I) q 2
      (diagonal_weights q) g s, diagonal_basis, TensorProduct.smul_tmul_smul]
  simp only [qqueCharge, add_mul, AddChar.map_add_eq_mul]

def qqueHomEquiv (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :=
  (QquePhysicalExteriorCompleteness.exteriorEquiv (diagonal q) (diagonal u) (diagonal e)).trans
    ((qqueSymmetricEquiv q u e).trans (SymmetricTensorFunctional.equiv _ _))

def qqueEquiv (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :=
  (qqueHomEquiv q u e).trans (invariantEquiv _ qqueBasis (qqueCharge q u e) (qque_weights q u e))

theorem qque_finrank (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :
    Module.finrank ℂ (QquePhysicalExteriorCompleteness.Sector (diagonal q) (diagonal u) (diagonal e)) =
      Fintype.card {i // qqueCharge q u e i=0} := by
  rw [(qqueEquiv q u e).finrank_eq]; simp

theorem qque_allowed (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :
    Allowed (QquePhysicalExteriorCompleteness.Sector (diagonal q) (diagonal u) (diagonal e)) ↔
      ∃ i, qqueCharge q u e i=0 := by
  rw [allowed_equiv (qqueHomEquiv q u e)]
  exact CyclicWeightCoordinates.allowed_iff _ _ _ (qque_weights q u e)

theorem duql_forbidden (d : I → ZMod N) (u : J → ZMod N) (q : K → ZMod N) (l : L → ZMod N) :
    Forbidden (DuqlExteriorCompleteness.Sector (diagonal d) (diagonal u) (diagonal q) (diagonal l)) ↔
      ∀ i, fourCharge d u q l i ≠ 0 := by
  rw [forbidden_iff_not_allowed, duql_allowed]
  simp

theorem qque_forbidden (q : I → ZMod N) (u : J → ZMod N) (e : K → ZMod N) :
    Forbidden (QquePhysicalExteriorCompleteness.Sector (diagonal q) (diagonal u) (diagonal e)) ↔
      ∀ i, qqueCharge q u e i ≠ 0 := by
  rw [forbidden_iff_not_allowed, qque_allowed]
  simp

theorem duue_forbidden (u : I → ZMod N) (d : J → ZMod N) (e : K → ZMod N) :
    Forbidden (DuueExchange.Sector (diagonal u) (diagonal d) (diagonal e)) ↔
      ∀ i, fourCharge u u d e i ≠ 0 := by
  rw [forbidden_iff_not_allowed, duue_allowed]
  simp

theorem llhh_forbidden (l : I → ZMod N) :
    Forbidden (WeinbergSMInterface.ModelSector (diagonal l)) ↔
      ∀ s, symmetricCharge 2 l s ≠ 0 := by
  rw [forbidden_iff_not_allowed, llhh_allowed]
  simp

end
end Physics.FlavoredCyclicCoordinates
