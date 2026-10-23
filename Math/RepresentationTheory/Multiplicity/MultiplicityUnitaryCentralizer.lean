import Math.RepresentationTheory.Multiplicity.IsometricMultiplicity
import Math.RepresentationTheory.Multiplicity.HilbertMultiplicityOperator
import Math.RepresentationTheory.Decomposition.ProductFactorization

/-!
# Unitary centralizers are products of multiplicity unitary groups

The explicit scalar-mixing action is faithful. Its dimension equals that of
the full commutant by the already checked algebraic classification, so it
exhausts all commuting operators. Unitarity uses its actual Hilbert adjoint,
and continuity of the inverse follows from its finite-dimensional linear
embedding, without a connectedness assumption.
-/

-- Bounded instance-search budget for concrete transport/equivalence types.
set_option synthInstance.maxHeartbeats 200000

namespace Math.MultiplicityUnitaryCentralizer

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MonoidAlgebra Math.IsometricMultiplicity
open HilbertMultiplicityOperator UnitaryCentralizerTransport

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E) (D : MultiplicityCommutant.Model ℂ[G] rho.asModule)
  [Fintype (isotypicComponents ℂ[G] rho.asModule)]

local instance simpleInner : ∀ c, InnerProductSpace ℂ (D.simple c) :=
  IsometricMultiplicity.simpleInnerProductSpace rho D

local instance simpleFinite : ∀ c, FiniteDimensional ℂ (D.simple c) :=
  fun c => MultiplicityCommutant.Model.simple_finiteDimensional (k := ℂ) D c

local instance simpleNontrivial : ∀ c, Nontrivial (D.simple c) := fun c => by
  let := D.isSimple c
  exact IsSimpleModule.nontrivial ℂ[G] (D.simple c)

local notation "H" => IsometricMultiplicity.Space rho D
local notation "tau" => IsometricMultiplicity.action rho D
local notation "P" => Matrices D.multiplicity
local notation "amp" => operator D.multiplicity (fun c => D.simple c)

/-- Mixing copies commutes with the actual group action on every constituent. -/
def intertwiner (A : P) : Representation.IntertwiningMap tau tau where
  toLinearMap := (amp A).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro c
    apply PiLp.ext
    intro a
    change (∑ b, A c a b • (IsometricMultiplicity.constituent rho D c g (x c b))) =
      IsometricMultiplicity.constituent rho D c g (∑ b, A c a b • x c b)
    simp

/-- The explicit matrix action, inside the full algebra of intertwiners. -/
def amplification : P →ₐ[ℂ] Representation.IntertwiningMap tau tau where
  toFun := intertwiner rho D
  map_one' := by
    apply Representation.IntertwiningMap.ext
    exact congrArg ContinuousLinearMap.toLinearMap (amp).map_one
  map_mul' A B := by
    apply Representation.IntertwiningMap.ext
    exact congrArg ContinuousLinearMap.toLinearMap ((amp).map_mul A B)
  map_zero' := by
    apply Representation.IntertwiningMap.ext
    exact congrArg ContinuousLinearMap.toLinearMap (amp).map_zero
  map_add' A B := by
    apply Representation.IntertwiningMap.ext
    exact congrArg ContinuousLinearMap.toLinearMap ((amp).map_add A B)
  commutes' z := by
    apply Representation.IntertwiningMap.ext
    exact congrArg ContinuousLinearMap.toLinearMap ((amp).commutes z)

theorem amplification_injective : Function.Injective (amplification rho D) := by
  intro A B h
  apply operator_injective D.multiplicity (fun c => D.simple c)
  apply ContinuousLinearMap.coe_injective
  exact congrArg Representation.IntertwiningMap.toLinearMap h

/-- An algebraic comparison used only to count dimensions, not to transport unitarity. -/
def dimensionEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    Representation.IntertwiningMap tau tau ≃ₐ[ℂ] P := by
  let := rho.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mp
    (UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary rho h)
  let e := (ProductFactorization.ofModulePrimeAsModuleEquiv (k := ℂ) (G := G) H).trans
    (IsometricMultiplicity.algebraicEquiv rho D h).symm
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := tau)).trans
    ((e.conjAlgEquiv ℂ).trans D.endAlgEquiv)

/-- No commuting operators are omitted by the explicit multiplicity action. -/
theorem amplification_surjective (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    Function.Surjective (amplification rho D) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (amplification rho D).toLinearMap)
    (dimensionEquiv rho D h).toLinearEquiv.finrank_eq.symm).mp (amplification_injective rho D)

/-- Actual, not merely abstract, matrix coordinates for every Hilbert-model intertwiner. -/
def amplificationEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    P ≃ₐ[ℂ] Representation.IntertwiningMap tau tau :=
  AlgEquiv.ofBijective (amplification rho D)
    ⟨amplification_injective rho D, amplification_surjective rho D h⟩

theorem operator_commutes (A : P) (g : G) (x : H) :
    amp A (tau g x) = tau g (amp A x) :=
  Representation.IntertwiningMap.isIntertwining tau tau (intertwiner rho D A) g x

theorem operator_exhausts (h : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (T : Representation.IntertwiningMap tau tau) :
    ∃ A : P, (amp A).toLinearMap = T.toLinearMap := by
  obtain ⟨A, hA⟩ := amplification_surjective rho D h T
  exact ⟨A, congrArg Representation.IntertwiningMap.toLinearMap hA⟩

/-- The product of multiplicity unitary matrices acts in the actual U centralizer. -/
def unitaryMap : (Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ) →*
    unitaryCentralizer tau where
  toFun A := ⟨⟨amp (fun c => A c),
    (operator_mem_unitary_iff D.multiplicity (fun c => D.simple c) _).mpr
      (fun c => (A c).2)⟩, fun g => by
        apply ContinuousLinearMap.ext
        intro x
        exact operator_commutes rho D (fun c => A c) g x⟩
  map_one' := Subtype.ext (Subtype.ext (amp).map_one)
  map_mul' A B := Subtype.ext (Subtype.ext ((amp).map_mul (fun c => A c) (fun c => B c)))

theorem unitaryMap_injective : Function.Injective (unitaryMap rho D) := by
  intro A B h
  have hab := operator_injective D.multiplicity (fun c => D.simple c)
    (congrArg (fun u : unitaryCentralizer tau => u.val.val) h)
  funext c
  exact Subtype.ext (congrFun hab c)

theorem unitaryMap_surjective (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    Function.Surjective (unitaryMap rho D) := by
  intro u
  let T : Representation.IntertwiningMap tau tau :=
    ⟨u.val.val.toLinearMap, fun g => congrArg ContinuousLinearMap.toLinearMap (u.2 g).eq⟩
  let A : P := (amplificationEquiv rho D h).symm T
  have hT : amplification rho D A = T := (amplificationEquiv rho D h).apply_symm_apply T
  have hop : amp A = u.val.val := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun R : Representation.IntertwiningMap tau tau => R.toLinearMap x) hT
  have hunit := (operator_mem_unitary_iff D.multiplicity (fun c => D.simple c) A).mp
    (hop.symm ▸ u.val.property)
  exact ⟨fun c => ⟨A c, hunit c⟩, Subtype.ext (Subtype.ext hop)⟩

theorem continuous_unitaryMap : Continuous (unitaryMap rho D) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_operator D.multiplicity (fun c => D.simple c)).comp
    (continuous_pi fun c => (continuous_apply c).subtype_val)

/-- The Hilbert-model centralizer is the full product, with its product topology. -/
def modelUnitaryEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    (Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ) ≃ₜ* unitaryCentralizer tau := by
  let e := MulEquiv.ofBijective (unitaryMap rho D)
    ⟨unitaryMap_injective rho D, unitaryMap_surjective rho D h⟩
  refine { e with
    continuous_toFun := continuous_unitaryMap rho D
    continuous_invFun := ?_ }
  let coeff : unitaryCentralizer tau → P := fun u c => e.symm u c
  have hc : Continuous coeff := by
    apply (isClosedEmbedding_operator D.multiplicity (fun c => D.simple c)).isEmbedding.isInducing.continuous_iff.mpr
    have he : amp ∘ coeff = (fun u : unitaryCentralizer tau => u.val.val) := by
      funext u
      have he' : unitaryMap rho D (e.symm u) = u := e.apply_symm_apply u
      exact congrArg (fun v : unitaryCentralizer tau => v.val.val) he'
    exact (continuous_subtype_val.comp continuous_subtype_val).congr
      (fun u => (congrFun he u).symm)
  exact continuous_pi fun c => ((continuous_apply c).comp hc).subtype_mk _

/-- The unitary centralizer of the original representation, including repeated constituents. -/
def unitaryCentralizerEquiv (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    unitaryCentralizer rho ≃ₜ* Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ :=
  (IsometricMultiplicity.unitaryCentralizerEquiv rho D h).trans (modelUnitaryEquiv rho D h).symm

end

end Math.MultiplicityUnitaryCentralizer
