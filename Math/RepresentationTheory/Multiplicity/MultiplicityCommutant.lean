import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Group.Pi.Units

/-!
# Multiplicity matrices for semisimple commutants

The index set is the actual set of nonzero isotypic components. Each component
is equipped with a proved equivalence to finitely many copies of a simple
module. Schur's lemma then identifies its endomorphisms with scalar matrices.
Only the represented module is assumed semisimple, not its acting algebra.
These are algebraic equivalences; no compatibility with an inner product is
asserted here.
-/

namespace Math.MultiplicityCommutant

noncomputable section

section Modules

variable (k R M : Type*) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

/-- A finite-copy realization of each actual isotypic component. -/
structure Model where
  multiplicity : isotypicComponents R M → ℕ
  positive : ∀ c, NeZero (multiplicity c)
  simple : (c : isotypicComponents R M) → Submodule R c.1
  isSimple : ∀ c, IsSimpleModule R (simple c)
  equiv : ∀ c, c.1 ≃ₗ[R] (Fin (multiplicity c) → simple c)

variable [FiniteDimensional k M]

instance component_finiteDimensional (c : isotypicComponents R M) :
    FiniteDimensional k c.1 :=
  FiniteDimensional.of_injective (c.1.subtype.restrictScalars k) c.1.subtype_injective

omit [IsAlgClosed k] in
include k in
/-- Existence follows from mathlib's isotypic finite-copy decomposition. -/
theorem exists_model [IsSemisimpleModule R M] : Nonempty (Model R M) := by
  have : IsNoetherian R M := isNoetherian_of_tower k inferInstance
  choose d hd S hS e using fun c : isotypicComponents R M =>
    (IsIsotypic.isotypicComponents c.2).linearEquiv_fun
  exact ⟨⟨d, hd, S, hS, fun c => (e c).some⟩⟩

variable {k R M}

/-- Scalar endomorphisms exhaust a finite-dimensional simple module. -/
def scalarEndEquiv (S : Type*) [AddCommGroup S] [Module k S] [Module R S]
    [IsScalarTower k R S] [FiniteDimensional k S] [IsSimpleModule R S] :
    Module.End R S ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End R S))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)).symm

namespace Model

variable (D : Model R M)

instance simple_finiteDimensional (c : isotypicComponents R M) :
    FiniteDimensional k (D.simple c) :=
  FiniteDimensional.of_injective
    ((D.simple c).subtype.restrictScalars k)
    (D.simple c).subtype_injective

omit [IsAlgClosed k] in
/-- The multiplicity really counts copies of the chosen simple constituent. -/
theorem component_finrank (c : isotypicComponents R M) :
    Module.finrank k c.1 = D.multiplicity c * Module.finrank k (D.simple c) := by
  rw [(D.equiv c).restrictScalars k |>.finrank_eq, Module.finrank_pi_fintype]
  simp

omit [IsAlgClosed k] in
include k in
/-- Copy counts are intrinsic, although the chosen constituent and coordinates are not. -/
theorem multiplicity_eq (D' : Model R M) (c : isotypicComponents R M) :
    D.multiplicity c = D'.multiplicity c := by
  let _ := D.isSimple c
  let _ := D'.isSimple c
  have : Nontrivial (D.simple c) := IsSimpleModule.nontrivial R (D.simple c)
  obtain ⟨e⟩ := (IsIsotypic.isotypicComponents c.2) (D'.simple c) (D.simple c)
  have hd := (e.restrictScalars k).finrank_eq
  have he := (D.component_finrank (k := k) c).symm.trans (D'.component_finrank (k := k) c)
  rw [← hd] at he
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := k) (M := D.simple c)) he

/-- A single isotypic component has a full matrix algebra of endomorphisms. -/
def componentEndEquiv (c : isotypicComponents R M) :
    Module.End R c.1 ≃ₐ[k]
      Matrix (Fin (D.multiplicity c)) (Fin (D.multiplicity c)) k := by
  let _ := D.isSimple c
  exact ((D.equiv c).conjAlgEquiv k).trans
    ((endVecAlgEquivMatrixEnd (Fin (D.multiplicity c)) k R (D.simple c)).trans
      (AlgEquiv.mapMatrix (scalarEndEquiv (R := R) (D.simple c))))

/-- The full commutant, including all mixing between repeated copies. -/
def endAlgEquiv [IsSemisimpleModule R M] :
    Module.End R M ≃ₐ[k]
      Π c : isotypicComponents R M,
        Matrix (Fin (D.multiplicity c)) (Fin (D.multiplicity c)) k := by
  classical
  exact (IsSemisimpleModule.endAlgEquiv k R M).trans
    (AlgEquiv.piCongrRight (D.componentEndEquiv (k := k)))

end Model

end Modules

section Representations

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (rho : Representation k G V)

omit [IsAlgClosed k] in
/-- The input is semisimplicity of the representation, not of the monoid algebra. -/
theorem exists_representation_model
    (h : Representation.IsSemisimpleRepresentation rho) :
    Nonempty (Model k[G] rho.asModule) := by
  let _ := (rho.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp h
  exact exists_model k k[G] rho.asModule

/-- The actual intertwiner algebra is the product of the multiplicity matrices. -/
def commutantEquiv (h : Representation.IsSemisimpleRepresentation rho)
    (D : Model k[G] rho.asModule) :
    rho.IntertwiningMap rho ≃ₐ[k]
      Π c : isotypicComponents k[G] rho.asModule,
        Matrix (Fin (D.multiplicity c)) (Fin (D.multiplicity c)) k := by
  let _ := (rho.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp h
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := rho)).trans D.endAlgEquiv

omit [IsAlgClosed k] in
/-- Finite dimension makes the intrinsic set of isotypic components finite. -/
theorem finite_components : Finite (isotypicComponents k[G] rho.asModule) := by
  have : IsNoetherian k[G] rho.asModule := isNoetherian_of_tower k inferInstance
  infer_instance

/-- Invertible equivariant maps allow arbitrary general-linear mixing of copies. -/
def automorphismEquiv (h : Representation.IsSemisimpleRepresentation rho)
    (D : Model k[G] rho.asModule) :
    (rho.IntertwiningMap rho)ˣ ≃*
      Π c : isotypicComponents k[G] rho.asModule,
        (Matrix (Fin (D.multiplicity c)) (Fin (D.multiplicity c)) k)ˣ :=
  (Units.mapEquiv (commutantEquiv rho h D).toMulEquiv).trans MulEquiv.piUnits

/-- The commutant dimension is the sum of squares of the multiplicities. -/
theorem commutant_finrank (h : Representation.IsSemisimpleRepresentation rho)
    (D : Model k[G] rho.asModule) [Fintype (isotypicComponents k[G] rho.asModule)] :
    Module.finrank k (rho.IntertwiningMap rho) = ∑ c, D.multiplicity c ^ 2 := by
  rw [(commutantEquiv rho h D).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_matrix, pow_two]

end Representations

end

end Math.MultiplicityCommutant
