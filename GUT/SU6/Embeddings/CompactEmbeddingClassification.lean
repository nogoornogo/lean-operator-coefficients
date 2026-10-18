import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import GUT.SU6.Representations.FundamentalRepresentation
import GUT.SU6.Embeddings.SemisimpleEmbedding
import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Tactic

open Math

/-!
# Concrete input for the semisimple embedding classification

`SemisimpleEmbedding.SixDimensionalBranchCounts.classify` proves the finite
arithmetic core of Claim semisimple embedding classification.  This module supplies a second rigorous piece of
that claim: the weak-center obstruction which excludes the
`(3,1) + (1,3)` branch.

The full classification of continuous homomorphisms
`SU(3) x SU(2) -> SU(6)` is intentionally not asserted here.  It still needs
the following representation-theoretic bridge:

1. complete reducibility of the restricted defining representation;
2. classification of complex `SU(3)` irreducibles of dimension at most six;
3. classification of complex `SU(2)` irreducibles of dimension at most six;
4. decomposition into product irreducibles (now supplied by
   `ProductFactorization`, downstream of this file);
5. exclusion of the irreducible `(3,2)` branch by its scalar commutant, once a
   nontrivial commuting hypercharge circle is required.

Keeping those inputs explicit avoids turning an arbitrary block list into a
purported decomposition certificate.
-/

namespace GUT
namespace CompactEmbeddingClassification

open Math.CompactEmbeddingClassification

open SemisimpleEmbedding

noncomputable section

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev SU6 := Matrix.specialUnitaryGroup (Fin 6) ℂ
abbrev ProductGroup := SU3 × SU2
abbrev RepSpace := Fin 6 -> ℂ
abbrev EuclideanRepSpace := EuclideanSpace ℂ (Fin 6)

/-- The defining `SU(6)` representation restricted along a proposed embedding. -/
def definingRestriction (ι : ProductGroup →* SU6) :
    Representation ℂ ProductGroup RepSpace :=
  FundamentalRepresentation.rho.comp ι

/-!
## Complete reducibility of finite-dimensional unitary representations

This is the unitary trick in the form needed by semisimple embedding classification.  It applies to arbitrary
groups: compactness is unnecessary once an invariant positive-definite inner
product is already available.
-/

/-!
## Applying the unitary trick to a proposed embedding
-/

/-- Matrix multiplication on the Euclidean model of `ℂ⁶`. -/
def euclideanDefiningRestriction (ι : ProductGroup →* SU6) :
    Representation ℂ ProductGroup EuclideanRepSpace where
  toFun g := Matrix.toEuclideanLin
    (((ι g : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' := by
    intro g h
    change
      Matrix.toEuclideanLin
          (((ι (g * h) : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) =
        Matrix.toEuclideanLin
            (((ι g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) *
          Matrix.toEuclideanLin
            (((ι h : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
    rw [map_mul]
    rw [Module.End.mul_eq_comp]
    exact Matrix.toLpLin_mul_same 2 _ _

/-- The Euclidean-norm model and the ordinary function-space model carry
equivalent restricted defining representations. -/
def euclideanDefiningRestrictionEquiv (ι : ProductGroup →* SU6) :
    Representation.Equiv (euclideanDefiningRestriction ι)
      (definingRestriction ι) where
  toLinearEquiv := WithLp.linearEquiv 2 ℂ RepSpace
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- A matrix satisfying `Mᴴ M = 1` preserves the Euclidean inner product. -/
theorem unitaryMatrix_preserves_inner
    (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hM : M.conjTranspose * M = 1)
    (x y : EuclideanRepSpace) :
    inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M y) =
      inner ℂ x y := by
  let A : EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace :=
    Matrix.toEuclideanLin M
  have hAdjoint : A.adjoint ∘ₗ A = LinearMap.id := by
    change
      (Matrix.toEuclideanLin M).adjoint ∘ₗ Matrix.toEuclideanLin M =
        LinearMap.id
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [← Matrix.toLpLin_mul_same]
    rw [hM]
    exact Matrix.toLpLin_one 2
  calc
    inner ℂ (A x) (A y) = inner ℂ x (A.adjoint (A y)) :=
      (LinearMap.adjoint_inner_right A x (A y)).symm
    _ = inner ℂ x y := by
      rw [← LinearMap.comp_apply, hAdjoint]
      rfl

theorem euclideanDefiningRestriction_unitary (ι : ProductGroup →* SU6) :
    IsUnitaryRepresentation (euclideanDefiningRestriction ι) := by
  intro g x y
  apply unitaryMatrix_preserves_inner
  have hUnitary :
      (((ι g : SU6) : Matrix (Fin 6) (Fin 6) ℂ) :
          Matrix (Fin 6) (Fin 6) ℂ) ∈ Matrix.unitaryGroup (Fin 6) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup (ι g).prop
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hUnitary)

/-- The defining representation restricted along any homomorphism into
`SU(6)` is completely reducible. -/
theorem euclideanDefiningRestriction_semisimple (ι : ProductGroup →* SU6) :
    Representation.IsSemisimpleRepresentation
      (euclideanDefiningRestriction ι) :=
  isSemisimpleRepresentation_of_unitary
    (euclideanDefiningRestriction ι)
    (euclideanDefiningRestriction_unitary ι)

/-!
## The scalar-commutant obstruction
-/

section ScalarCommutant

variable {G E : Type*} [Monoid G]
variable [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

/-- Schur's lemma over `ℂ`: every endomorphism commuting with an irreducible
representation is scalar. -/
theorem intertwiner_eq_smul_one_of_irreducible
    (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (f : Representation.IntertwiningMap ρ ρ) :
    ∃ c : ℂ, f = c • 1 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 f
  exact ⟨c, by simpa using hc.symm⟩

/-- A precise algebraic necessary condition for a commuting hypercharge action:
the commutant contains a non-scalar operator. -/
def HasNonscalarCommutant (ρ : Representation ℂ G E) : Prop :=
  ∃ f : Representation.IntertwiningMap ρ ρ, ∀ c : ℂ, f ≠ c • 1

theorem not_hasNonscalarCommutant_of_irreducible
    (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ] :
    ¬ HasNonscalarCommutant ρ := by
  rintro ⟨f, hf⟩
  obtain ⟨c, hc⟩ := intertwiner_eq_smul_one_of_irreducible ρ f
  exact hf c hc

end ScalarCommutant

/-- A scalar matrix in `SU(6)` has scalar coefficient in the finite group of
sixth roots of unity. -/
theorem scalar_coefficient_pow_six_of_mem_su6
    (g : SU6) (c : ℂ)
    (hScalar :
      ((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ) =
        c • (1 : Matrix (Fin 6) (Fin 6) ℂ)) :
    c ^ 6 = 1 := by
  have hDet :
      Matrix.det (((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) = 1 :=
    g.prop.2
  rw [hScalar] at hDet
  simpa using hDet

/-!
## The nontrivial center of `SU(2)`
-/

/-- The matrix `-I₂`, viewed as the nontrivial central element of `SU(2)`. -/
def su2CenterElement : SU2 :=
  ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      simp
    · simp [Matrix.det_neg]⟩

theorem su2CenterElement_coe :
    ((su2CenterElement : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 :=
  rfl

theorem su2CenterElement_ne_one : su2CenterElement ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun M : SU2 => ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) h
  norm_num [su2CenterElement] at h00

theorem su2CenterElement_sq : su2CenterElement * su2CenterElement = 1 := by
  apply Subtype.ext
  simp [su2CenterElement]

theorem su2CenterElement_central (g : SU2) :
    su2CenterElement * g = g * su2CenterElement := by
  apply Subtype.ext
  simp [su2CenterElement]

/-- The weak-center element `(1,-I₂)` in the semisimple product. -/
def weakCenterElement : ProductGroup := (1, su2CenterElement)

theorem weakCenterElement_ne_one : weakCenterElement ≠ 1 := by
  intro h
  exact su2CenterElement_ne_one (congrArg Prod.snd h)

theorem weakCenterElement_sq : weakCenterElement * weakCenterElement = 1 := by
  apply Prod.ext
  · simp [weakCenterElement]
  · exact su2CenterElement_sq

theorem weakCenterElement_central (g : ProductGroup) :
    weakCenterElement * g = g * weakCenterElement := by
  apply Prod.ext
  · simp [weakCenterElement]
  · exact su2CenterElement_central g.2

/-!
## Excluding weak doublets when the weak center is killed
-/

/-- A product-group representation detects the weak center if that element
moves at least one vector.  The defining weak doublet has this property. -/
def DetectsWeakCenter
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (σ : Representation ℂ ProductGroup W) : Prop :=
  ∃ w, σ weakCenterElement w ≠ w

/--
If a proposed homomorphism kills `(1,-I₂)`, no representation obtained by
restriction from `SU(6)` can contain an injectively embedded representation
which detects that element.

This is the precise group-level obstruction behind the statement that the
`(3,1) + (1,3)` branch has only integer weak isospin.
-/
theorem no_weakCenter_detecting_subrepresentation_of_center_mem_ker
    (ι : ProductGroup →* SU6)
    (hCenter : ι weakCenterElement = 1)
    {V W : Type*}
    [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W]
    (ρ : Representation ℂ SU6 V)
    (σ : Representation ℂ ProductGroup W)
    (hDetects : DetectsWeakCenter σ) :
    ¬ ∃ f : Representation.IntertwiningMap σ (ρ.comp ι),
        Function.Injective f := by
  exact no_kernel_detecting_subrepresentation
    ι ρ σ weakCenterElement hCenter hDetects

/-- The same obstruction specialized to the restricted defining action. -/
theorem no_weakCenter_detecting_subrepresentation_of_definingRestriction
    (ι : ProductGroup →* SU6)
    (hCenter : ι weakCenterElement = 1)
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (σ : Representation ℂ ProductGroup W)
    (hDetects : DetectsWeakCenter σ) :
    ¬ ∃ f : Representation.IntertwiningMap σ (definingRestriction ι),
        Function.Injective f := by
  exact no_weakCenter_detecting_subrepresentation_of_center_mem_ker
    ι hCenter FundamentalRepresentation.rho σ hDetects

end

end CompactEmbeddingClassification
end GUT
