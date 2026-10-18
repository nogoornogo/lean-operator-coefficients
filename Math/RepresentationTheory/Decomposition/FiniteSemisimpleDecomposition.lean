import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Math.RepresentationTheory.Decomposition.ProductFactorization
import Mathlib.RepresentationTheory.Semisimple

/-!
# Finite decompositions of semisimple representations

This file packages mathlib's finite direct-sum decomposition of a finite
semisimple module in representation-theoretic form.  It is the bridge needed
to apply irreducible product factorization separately to every constituent of
the restricted six-dimensional defining representation.
-/

namespace Math
namespace FiniteSemisimpleDecomposition

open ContinuousRepresentationScope
open scoped MonoidAlgebra

noncomputable section

variable {G V : Type*} [Group G]
variable [AddCommGroup V] [Module ℂ V]

/-- A finite group-algebra direct-sum decomposition into simple submodules. -/
structure Decomposition (rho : Representation ℂ G V) where
  numberOfBlocks : ℕ
  block : Fin numberOfBlocks → Submodule ℂ[G] rho.asModule
  equiv : rho.asModule ≃ₗ[ℂ[G]] Π₀ i : Fin numberOfBlocks, block i
  simple : ∀ i, IsSimpleModule ℂ[G] (block i)

/-- A finite-dimensional semisimple representation admits a finite
decomposition into simple group-algebra submodules. -/
theorem exists_decomposition
    (rho : Representation ℂ G V)
    [FiniteDimensional ℂ V]
    (hSemisimple : Representation.IsSemisimpleRepresentation rho) :
    Nonempty (Decomposition rho) := by
  let : IsSemisimpleModule ℂ[G] rho.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp
      hSemisimple
  let : Module.Finite ℂ[G] rho.asModule := by
    exact Module.Finite.of_restrictScalars_finite ℂ ℂ[G] rho.asModule
  obtain ⟨n, S, e, hS⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] rho.asModule
  exact ⟨⟨n, S, e, hS⟩⟩

namespace Decomposition

variable {rho : Representation ℂ G V}

/-- A simple group-algebra summand viewed as a subrepresentation of `rho`. -/
def subrepresentation (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Subrepresentation rho :=
  Subrepresentation.ofSubmodule' (D.block i)

/-- The abstract representation carried by one group-algebra summand. -/
def blockRepresentation (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Representation ℂ G (D.block i) :=
  Representation.ofModule' (D.block i)

/-- The direct sum of the abstract simple representations carried by all
blocks of a decomposition. -/
def directSumRepresentation (D : Decomposition rho) :
    Representation ℂ G (Π₀ i : Fin D.numberOfBlocks, D.block i) :=
  Representation.directSum fun i => D.blockRepresentation i

/-- The group-algebra decomposition equivalence is an equivalence of the
original representation with the direct sum of its abstract simple blocks. -/
def representationEquivDirectSum (D : Decomposition rho) :
    Representation.Equiv rho D.directSumRepresentation where
  toLinearEquiv :=
    rho.asModuleEquiv.symm.trans (D.equiv.restrictScalars ℂ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply DFinsupp.ext
    intro i
    change
      (D.equiv (rho.asModuleEquiv.symm (rho g v))) i =
        D.blockRepresentation i g
          ((D.equiv (rho.asModuleEquiv.symm v)) i)
    rw [rho.asModuleEquiv_symm_map_rho, map_smul, DFinsupp.smul_apply,
      MonoidAlgebra.of_apply]
    rfl

/-- The abstract summand and its ambient invariant-subspace realization are
equivalent representations. -/
def blockAmbientEquiv (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Representation.Equiv (D.blockRepresentation i)
      (D.subrepresentation i).toRepresentation := by
  let f : Representation.IntertwiningMap (D.blockRepresentation i)
      (D.subrepresentation i).toRepresentation :=
    { toLinearMap :=
        { toFun := fun s => ⟨s.1, s.2⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      isIntertwining' g := by
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        change
          ((MonoidAlgebra.single g (1 : ℂ)) • (s : rho.asModule) : V) =
            rho g s.1
        rw [Representation.single_smul, one_smul]
        rfl }
  exact Representation.IntertwiningMap.ofBijective f
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun y =>
      ⟨⟨y.1, y.2⟩, Subtype.ext rfl⟩⟩

/-- Every abstract block representation in a semisimple decomposition is
irreducible. -/
theorem blockRepresentation_isIrreducible
    (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Representation.IsIrreducible (D.blockRepresentation i) := by
  let : IsSimpleModule ℂ[G] (D.block i) := D.simple i
  let : IsSimpleModule ℂ[G] (D.blockRepresentation i).asModule :=
    IsSimpleModule.congr
      (ProductFactorization.ofModulePrimeAsModuleEquiv (D.block i))
  exact (Representation.irreducible_iff_isSimpleModule_asModule
    (D.blockRepresentation i)).mpr inferInstance

theorem subrepresentation_isIrreducible
    (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Representation.IsIrreducible (D.subrepresentation i).toRepresentation := by
  let : Representation.IsIrreducible (D.blockRepresentation i) :=
    D.blockRepresentation_isIrreducible i
  exact ProductFactorization.isIrreducible_of_equiv (D.blockAmbientEquiv i).symm

/-- The dimensions of the simple constituents add to the ambient dimension. -/
theorem sum_finrank
    (D : Decomposition rho) [FiniteDimensional ℂ V] :
    ∑ i, Module.finrank ℂ (D.block i) = Module.finrank ℂ V := by
  let (i : Fin D.numberOfBlocks) : FiniteDimensional ℂ (D.block i) :=
    FiniteDimensional.of_injective
      ((D.block i).subtype.restrictScalars ℂ) (D.block i).subtype_injective
  rw [← Module.finrank_directSum]
  exact (D.equiv.restrictScalars ℂ).finrank_eq.symm

/-- Each constituent has dimension at most the ambient representation. -/
theorem block_finrank_le
    (D : Decomposition rho) [FiniteDimensional ℂ V]
    (i : Fin D.numberOfBlocks) :
    Module.finrank ℂ (D.block i) ≤ Module.finrank ℂ V := by
  let : FiniteDimensional ℂ (D.block i) :=
    FiniteDimensional.of_injective
      ((D.block i).subtype.restrictScalars ℂ) (D.block i).subtype_injective
  exact Submodule.finrank_le (D.subrepresentation i).toSubmodule

/-- If one simple constituent already has the full ambient dimension, its
inclusion is an equivalence and the ambient representation is irreducible. -/
theorem irreducible_of_block_finrank_eq
    (D : Decomposition rho) [FiniteDimensional ℂ V]
    (i : Fin D.numberOfBlocks)
    (hDimension : Module.finrank ℂ (D.block i) = Module.finrank ℂ V) :
    Representation.IsIrreducible rho := by
  have hTop : (D.subrepresentation i).toSubmodule = ⊤ :=
    Submodule.eq_top_of_finrank_eq hDimension
  let inclusion : Representation.IntertwiningMap
      (D.subrepresentation i).toRepresentation rho :=
    { toLinearMap := (D.subrepresentation i).toSubmodule.subtype
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        rfl }
  have hBijective : Function.Bijective inclusion := by
    constructor
    · exact (D.subrepresentation i).toSubmodule.subtype_injective
    · intro v
      refine ⟨⟨v, ?_⟩, rfl⟩
      rw [hTop]
      exact Submodule.mem_top
  let e := Representation.IntertwiningMap.ofBijective inclusion hBijective
  let : Representation.IsIrreducible
      (D.subrepresentation i).toRepresentation :=
    D.subrepresentation_isIrreducible i
  exact ProductFactorization.isIrreducible_of_equiv e.symm

/-- If a group element acts trivially on every simple constituent, then it
acts trivially on the whole semisimple representation. -/
theorem action_eq_id_of_forall_block
    (D : Decomposition rho) (g : G)
    (hBlocks : ∀ i,
      (D.subrepresentation i).toRepresentation g = LinearMap.id) :
    rho g = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply rho.asModuleEquiv.symm.injective
  rw [rho.asModuleEquiv_symm_map_rho]
  apply D.equiv.injective
  rw [map_smul]
  apply DFinsupp.ext
  intro i
  change
    (MonoidAlgebra.single g (1 : ℂ)) •
        (D.equiv (rho.asModuleEquiv.symm v)) i =
      (D.equiv (rho.asModuleEquiv.symm v)) i
  let x := (D.equiv (rho.asModuleEquiv.symm v)) i
  apply Subtype.ext
  change
    ((MonoidAlgebra.single g (1 : ℂ)) • (x : rho.asModule) : V) = x.1
  rw [Representation.single_smul, one_smul]
  have hx := LinearMap.congr_fun (hBlocks i)
    (⟨x.1, x.2⟩ : (D.subrepresentation i).toSubmodule)
  exact congrArg Subtype.val hx

variable [TopologicalSpace G] [TopologicalSpace V]

/-- Every constituent inherits joint continuity from the ambient action. -/
theorem subrepresentation_jointlyContinuous
    (D : Decomposition rho) (i : Fin D.numberOfBlocks)
    (hContinuous : IsJointlyContinuous rho) :
    IsJointlyContinuous (D.subrepresentation i).toRepresentation :=
  hContinuous.subrepresentation (D.subrepresentation i)

end Decomposition

end

end FiniteSemisimpleDecomposition
end Math
