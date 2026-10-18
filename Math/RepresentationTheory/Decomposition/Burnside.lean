import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic

/-!
# A finite-dimensional Burnside lemma

Over an algebraically closed field, Schur's lemma and the Jacobson density
theorem imply that an algebra acting irreducibly on a finite-dimensional
vector space maps surjectively onto the full linear endomorphism algebra.
This is the algebraic input needed for irreducibility of external tensor
products.
-/

namespace Math
namespace Burnside

noncomputable section

variable {k A V : Type*}
variable [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup V] [Module k V] [Module A V]
variable [IsScalarTower k A V]
variable [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]

/-- Every `k`-linear endomorphism of a finite-dimensional simple `A`-module
is induced by an element of `A`. -/
theorem exists_smul_eq_linearMap (f : V →ₗ[k] V) :
    ∃ a : A, f = Algebra.lsmul k k V a := by
  classical
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro phi v
        obtain ⟨c, hc⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2 phi
        rw [← hc]
        change f (c • v) = c • f v
        exact f.map_smul c v }
  let b := Module.finBasis k V
  let s : Finset V := Finset.univ.image b
  obtain ⟨a, ha⟩ := jacobson_density F s
  refine ⟨a, ?_⟩
  apply b.ext
  intro i
  have hmem : b i ∈ s := by
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  exact ha (b i) hmem

/-- Equivalently, the action homomorphism into the full endomorphism algebra
is surjective. -/
theorem lsmul_surjective :
    Function.Surjective (Algebra.lsmul k k V : A → Module.End k V) := by
  intro f
  obtain ⟨a, ha⟩ := exists_smul_eq_linearMap (k := k) (A := A) f
  exact ⟨a, ha.symm⟩

section Representations

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- Burnside's theorem in representation form: the linear extension of a
finite-dimensional irreducible representation fills the entire endomorphism
algebra. -/
theorem representation_asAlgebraHom_surjective
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Function.Surjective rho.asAlgebraHom := by
  have hTower : IsScalarTower k k[G] rho.asModule :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule rho
  intro f
  obtain ⟨r, hr⟩ :=
    @exists_smul_eq_linearMap k k[G] rho.asModule
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      hTower inferInstance inferInstance inferInstance f
  refine ⟨r, ?_⟩
  rw [hr]
  rfl

end Representations

end

end Burnside
end Math
