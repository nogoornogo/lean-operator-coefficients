import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Math.RepresentationTheory.Decomposition.ProductFactorization

/-!
# Product factorization for finite-dimensional unitary representations

This file connects the algebraic product-factorization theorem to the
unitary setting used by semisimple embedding classification.  Unitarity descends to both factor restrictions,
so their semisimplicity is supplied by invariant orthogonal complements.
-/

namespace Math
namespace CompactProductFactorization

open CompactEmbeddingClassification ProductFactorization
open ExternalTensorProduct
open ContinuousRepresentationScope
open scoped MonoidAlgebra

noncomputable section

variable {G H E : Type*} [Group G] [Group H]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- A unitary product action remains unitary after restriction to the first
factor. -/
theorem firstRestriction_unitary
    (tau : Representation ℂ (G × H) E)
    (hUnitary : IsUnitaryRepresentation tau) :
    IsUnitaryRepresentation (firstRestriction tau) := by
  intro g x y
  exact hUnitary (g, 1) x y

omit [FiniteDimensional ℂ E] in
/-- A unitary product action remains unitary after restriction to the second
factor. -/
theorem secondRestriction_unitary
    (tau : Representation ℂ (G × H) E)
    (hUnitary : IsUnitaryRepresentation tau) :
    IsUnitaryRepresentation (secondRestriction tau) := by
  intro h x y
  exact hUnitary (1, h) x y

theorem firstRestriction_isSemisimple
    (tau : Representation ℂ (G × H) E)
    (hUnitary : IsUnitaryRepresentation tau) :
    Representation.IsSemisimpleRepresentation (firstRestriction tau) :=
  isSemisimpleRepresentation_of_unitary
    (firstRestriction tau) (firstRestriction_unitary tau hUnitary)

theorem secondRestriction_isSemisimple
    (tau : Representation ℂ (G × H) E)
    (hUnitary : IsUnitaryRepresentation tau) :
    Representation.IsSemisimpleRepresentation (secondRestriction tau) :=
  isSemisimpleRepresentation_of_unitary
    (secondRestriction tau) (secondRestriction_unitary tau hUnitary)

section ContinuousFactors

variable [TopologicalSpace G] [TopologicalSpace H]
variable {U : Type*} [AddCommGroup U] [Module ℂ U]

omit [FiniteDimensional ℂ E] in
/-- A first-factor group-algebra submodule, viewed as an invariant ambient
subspace, inherits joint continuity. -/
theorem firstSubmodule_jointlyContinuous
    (tau : Representation ℂ (G × H) E)
    (S : Submodule ℂ[G] (firstRestriction tau).asModule)
    (hContinuous : IsJointlyContinuous tau) :
    IsJointlyContinuous
      (Subrepresentation.ofSubmodule' S).toRepresentation := by
  have hFirst : IsJointlyContinuous (firstRestriction tau) :=
    hContinuous.comp (ContinuousMonoidHom.inl G H)
  exact hFirst.subrepresentation (Subrepresentation.ofSubmodule' S)

omit [FiniteDimensional ℂ E] in
/-- The concrete evaluation-image model of the multiplicity factor inherits
joint continuity from the ambient product representation. -/
theorem multiplicityRange_jointlyContinuous
    (tau : Representation ℂ (G × H) E)
    (rho : Representation ℂ G U) (u : U)
    (hContinuous : IsJointlyContinuous tau) :
    IsJointlyContinuous (multiplicityRangeRepresentation tau rho u) := by
  have hSecond : IsJointlyContinuous (secondRestriction tau) :=
    hContinuous.comp (ContinuousMonoidHom.inr G H)
  exact hSecond.subrepresentation (multiplicityRange tau rho u)

/-- Continuous ambient models for both factors selected from an irreducible
unitary product representation. -/
structure ContinuousFactorWitness
    (tau : Representation ℂ (G × H) E) where
  S : Submodule ℂ[G] (firstRestriction tau).asModule
  simple : IsSimpleModule ℂ[G] S
  u : S
  u_ne_zero : u ≠ 0
  firstFactor : IsContinuousFiniteDimensionalIrrep
    (firstSubmoduleAsSubrepresentation tau S).toRepresentation
  secondFactor : IsContinuousFiniteDimensionalIrrep
    (multiplicityRangeRepresentation tau
      (firstSubmoduleRepresentation tau S) u)

/-- The canonical external-tensor-product equivalence associated to a
continuous factor witness. -/
def ContinuousFactorWitness.productEquiv
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (F : ContinuousFactorWitness tau) :
    Representation.Equiv
      (externalTprod
        (firstSubmoduleRepresentation tau F.S)
        (multiplicityRepresentation tau
          (firstSubmoduleRepresentation tau F.S))) tau := by
  letI : IsSimpleModule ℂ[G] F.S := F.simple
  letI : Nontrivial F.S := IsSimpleModule.nontrivial ℂ[G] F.S
  letI : IsSimpleModule ℂ[G]
      (firstSubmoduleRepresentation tau F.S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv F.S)
  letI : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau F.S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau F.S)).mpr inferInstance
  letI : FiniteDimensional ℂ F.S :=
    FiniteDimensional.of_injective
      (firstSubmoduleInclusion tau F.S).toLinearMap
      (firstSubmoduleInclusion_injective tau F.S)
  have hInclusion : firstSubmoduleInclusion tau F.S ≠ 0 := by
    intro hzero
    obtain ⟨x, y, hxy⟩ := exists_pair_ne F.S
    apply hxy
    apply firstSubmoduleInclusion_injective tau F.S
    rw [hzero]
    rfl
  exact multiplicityEvaluationEquiv tau
    (firstSubmoduleRepresentation tau F.S)
    ⟨firstSubmoduleInclusion tau F.S, hInclusion⟩

/-- If the extracted first factor acts trivially at `g`, then the original
product representation acts trivially at `(g,1)`. -/
theorem ContinuousFactorWitness.first_action_eq_id
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (F : ContinuousFactorWitness tau) (g : G)
    (hFactor :
      (firstSubmoduleAsSubrepresentation tau F.S).toRepresentation g =
        LinearMap.id) :
    tau (g, 1) = LinearMap.id := by
  let : IsSimpleModule ℂ[G] F.S := F.simple
  let : Nontrivial F.S := IsSimpleModule.nontrivial ℂ[G] F.S
  let : IsSimpleModule ℂ[G]
      (firstSubmoduleRepresentation tau F.S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv F.S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau F.S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau F.S)).mpr inferInstance
  have hAbstract : firstSubmoduleRepresentation tau F.S g = LinearMap.id := by
    apply LinearMap.ext
    intro s
    let eFirst := firstSubmoduleAmbientEquiv tau F.S
    apply eFirst.toLinearEquiv.injective
    change eFirst.toLinearEquiv
      ((firstSubmoduleRepresentation tau F.S) g s) = eFirst.toLinearEquiv s
    have hs := LinearMap.congr_fun
      (eFirst.toIntertwiningMap.isIntertwining' g) s
    simp only [LinearMap.comp_apply] at hs
    calc
      eFirst.toLinearEquiv
          ((firstSubmoduleRepresentation tau F.S) g s) =
          (firstSubmoduleAsSubrepresentation tau F.S).toRepresentation g
            (eFirst.toLinearEquiv s) := hs
      _ = eFirst.toLinearEquiv s := by rw [hFactor]; rfl
  let e := F.productEquiv tau
  have hExternal :
      externalTprod
          (firstSubmoduleRepresentation tau F.S)
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau F.S)) (g, 1) =
        LinearMap.id := by
    rw [externalTprod_apply, hAbstract, map_one]
    exact TensorProduct.map_id
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx := LinearMap.congr_fun
    (e.toIntertwiningMap.isIntertwining' (g, 1)) x
  simp only [LinearMap.comp_apply] at hx
  calc
    tau (g, 1) (e x) =
        e (externalTprod
          (firstSubmoduleRepresentation tau F.S)
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau F.S)) (g, 1) x) :=
      hx.symm
    _ = e x := by rw [hExternal]; rfl
    _ = LinearMap.id (e x) := rfl

/-- If the extracted second factor acts trivially at `h`, then the original
product representation acts trivially at `(1,h)`. -/
theorem ContinuousFactorWitness.second_action_eq_id
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (F : ContinuousFactorWitness tau) (h : H)
    (hFactor :
      multiplicityRangeRepresentation tau
          (firstSubmoduleRepresentation tau F.S) F.u h =
        LinearMap.id) :
    tau (1, h) = LinearMap.id := by
  let : IsSimpleModule ℂ[G] F.S := F.simple
  let : Nontrivial F.S := IsSimpleModule.nontrivial ℂ[G] F.S
  let : IsSimpleModule ℂ[G]
      (firstSubmoduleRepresentation tau F.S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv F.S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau F.S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau F.S)).mpr inferInstance
  have hAbstract :
      multiplicityRepresentation tau
          (firstSubmoduleRepresentation tau F.S) h = LinearMap.id := by
    apply LinearMap.ext
    intro f
    let eSecond := multiplicityRangeEquiv tau
      (firstSubmoduleRepresentation tau F.S) F.u_ne_zero
    apply eSecond.toLinearEquiv.injective
    change eSecond.toLinearEquiv
      (multiplicityRepresentation tau
        (firstSubmoduleRepresentation tau F.S) h f) = eSecond.toLinearEquiv f
    have hf := LinearMap.congr_fun
      (eSecond.toIntertwiningMap.isIntertwining' h) f
    simp only [LinearMap.comp_apply] at hf
    calc
      eSecond.toLinearEquiv
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau F.S) h f) =
          multiplicityRangeRepresentation tau
            (firstSubmoduleRepresentation tau F.S) F.u h
              (eSecond.toLinearEquiv f) := hf
      _ = eSecond.toLinearEquiv f := by rw [hFactor]; rfl
  let e := F.productEquiv tau
  have hExternal :
      externalTprod
          (firstSubmoduleRepresentation tau F.S)
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau F.S)) (1, h) =
        LinearMap.id := by
    rw [externalTprod_apply, map_one, hAbstract]
    exact TensorProduct.map_id
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx := LinearMap.congr_fun
    (e.toIntertwiningMap.isIntertwining' (1, h)) x
  simp only [LinearMap.comp_apply] at hx
  calc
    tau (1, h) (e x) =
        e (externalTprod
          (firstSubmoduleRepresentation tau F.S)
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau F.S)) (1, h) x) :=
      hx.symm
    _ = e x := by rw [hExternal]; rfl
    _ = LinearMap.id (e x) := rfl

/-- The dimension of an irreducible product representation is the product of
the dimensions of the two continuous factor models in its witness. -/
theorem ContinuousFactorWitness.dimension_mul
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (F : ContinuousFactorWitness tau) :
    Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule *
      Module.finrank ℂ
        (MultiplicityRangeSpace tau
          (firstSubmoduleRepresentation tau F.S) F.u) =
      Module.finrank ℂ E := by
  let : IsSimpleModule ℂ[G] F.S := F.simple
  let : Nontrivial F.S := IsSimpleModule.nontrivial ℂ[G] F.S
  let : IsSimpleModule ℂ[G]
      (firstSubmoduleRepresentation tau F.S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv F.S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau F.S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau F.S)).mpr inferInstance
  let : FiniteDimensional ℂ F.S :=
    FiniteDimensional.of_injective
      (firstSubmoduleInclusion tau F.S).toLinearMap
      (firstSubmoduleInclusion_injective tau F.S)
  let : FiniteDimensional ℂ
      (MultiplicitySpace tau (firstSubmoduleRepresentation tau F.S)) :=
    FiniteDimensional.of_injective
      (multiplicityEvaluationAt tau
        (firstSubmoduleRepresentation tau F.S) F.u).toLinearMap
      (multiplicityEvaluationAt_injective tau
        (firstSubmoduleRepresentation tau F.S) F.u_ne_zero)
  have hInclusion : firstSubmoduleInclusion tau F.S ≠ 0 := by
    intro hzero
    obtain ⟨x, y, hxy⟩ := exists_pair_ne F.S
    apply hxy
    apply firstSubmoduleInclusion_injective tau F.S
    rw [hzero]
    rfl
  have hProduct :=
    (multiplicityEvaluationEquiv tau
      (firstSubmoduleRepresentation tau F.S)
      ⟨firstSubmoduleInclusion tau F.S, hInclusion⟩).toLinearEquiv.finrank_eq
  have hFirst :=
    (firstSubmoduleAmbientEquiv tau F.S).toLinearEquiv.finrank_eq
  have hSecond :=
    (multiplicityRangeEquiv tau
      (firstSubmoduleRepresentation tau F.S) F.u_ne_zero).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct] at hProduct
  rw [hFirst, hSecond] at hProduct
  exact hProduct

/-- The factors in the algebraic product decomposition can be chosen as
continuous finite-dimensional irreducible subrepresentations of the two
ambient restrictions. -/
theorem exists_continuousFactorWitness
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau) :
    Nonempty (ContinuousFactorWitness tau) := by
  have hFirstSemisimple := firstRestriction_isSemisimple tau hUnitary
  have hSecondSemisimple := secondRestriction_isSemisimple tau hUnitary
  obtain ⟨S, hS⟩ := exists_simple_firstSubmodule tau hFirstSemisimple
  let : IsSimpleModule ℂ[G] S := hS
  let : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
  let : IsSimpleModule ℂ[G]
      (firstSubmoduleRepresentation tau S).asModule :=
    IsSimpleModule.congr (ofModulePrimeAsModuleEquiv S)
  let : Representation.IsIrreducible
      (firstSubmoduleRepresentation tau S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (firstSubmoduleRepresentation tau S)).mpr inferInstance
  let : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective
      (firstSubmoduleInclusion tau S).toLinearMap
      (firstSubmoduleInclusion_injective tau S)
  have hInclusion : firstSubmoduleInclusion tau S ≠ 0 := by
    intro hzero
    obtain ⟨x, y, hxy⟩ := exists_pair_ne S
    apply hxy
    apply firstSubmoduleInclusion_injective tau S
    rw [hzero]
    rfl
  obtain ⟨u, hu⟩ := exists_ne (0 : S)
  have hFirstIrreducible :=
    firstSubmoduleAsSubrepresentation_isIrreducible tau S hS
  have hSecondIrreducible :=
    multiplicityRangeRepresentation_isIrreducible tau
      (firstSubmoduleRepresentation tau S) hu
      ⟨firstSubmoduleInclusion tau S, hInclusion⟩ hSecondSemisimple
  refine ⟨
    { S := S
      simple := hS
      u := u
      u_ne_zero := hu
      firstFactor := ?_
      secondFactor := ?_ }⟩
  · exact
      { finiteDimensional := inferInstance
        irreducible := hFirstIrreducible
        continuous_action := firstSubmodule_jointlyContinuous tau S hContinuous }
  · exact
      { finiteDimensional := inferInstance
        irreducible := hSecondIrreducible
        continuous_action := multiplicityRange_jointlyContinuous tau
          (firstSubmoduleRepresentation tau S) u hContinuous }

end ContinuousFactors

/-- Every nonzero irreducible finite-dimensional unitary representation of a
product group is equivalent to an external tensor product of irreducible
factor representations. -/
theorem exists_irreducible_externalTprod_equiv
    (tau : Representation ℂ (G × H) E)
    [Nontrivial E] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau) :
    ∃ S : Submodule ℂ[G] (firstRestriction tau).asModule,
      IsSimpleModule ℂ[G] S ∧
        Representation.IsIrreducible
          (firstSubmoduleRepresentation tau S) ∧
        Representation.IsIrreducible
          (multiplicityRepresentation tau
            (firstSubmoduleRepresentation tau S)) ∧
        Nonempty
          (Representation.Equiv
            (externalTprod
              (firstSubmoduleRepresentation tau S)
              (multiplicityRepresentation tau
                (firstSubmoduleRepresentation tau S)))
            tau) :=
  exists_irreducible_externalTprod_equiv_of_restrictions_semisimple tau
    (firstRestriction_isSemisimple tau hUnitary)
    (secondRestriction_isSemisimple tau hUnitary)

end

end CompactProductFactorization
end Math
