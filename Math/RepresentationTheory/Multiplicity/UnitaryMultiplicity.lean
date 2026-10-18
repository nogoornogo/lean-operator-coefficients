import Math.RepresentationTheory.Multiplicity.CommutantCentralizer
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Semisimplicity and algebraic multiplicities of unitary representations

The orthogonal-complement proof previously used in the SU(6) embedding
module applies to any group. It supplies semisimplicity of this module,
without assuming compactness or semisimplicity of the whole group algebra.
The resulting commutant equivalence is still algebraic: an arbitrary chosen
finite-copy equivalence need not preserve the inner product.
-/

namespace Math.UnitaryMultiplicity

noncomputable section

variable {G E : Type*} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def IsUnitaryRepresentation (rho : Representation ℂ G E) : Prop :=
  ∀ g x y, inner ℂ (rho g x) (rho g y) = inner ℂ x y

/-- The orthogonal complement is invariant under the same group action. -/
def orthogonalSubrepresentation
    (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) : Subrepresentation rho where
  toSubmodule := S.toSubmoduleᗮ
  apply_mem_toSubmodule g {x} hx := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    calc
      inner ℂ y (rho g x) = inner ℂ (rho g (rho g⁻¹ y)) (rho g x) := by simp
      _ = inner ℂ (rho g⁻¹ y) x := h g (rho g⁻¹ y) x
      _ = 0 := hx (rho g⁻¹ y) (S.apply_mem_toSubmodule g⁻¹ hy)

variable [FiniteDimensional ℂ E]

theorem isCompl_orthogonalSubrepresentation
    (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) : IsCompl S (orthogonalSubrepresentation rho h S) := by
  constructor
  · rw [disjoint_iff]
    apply Subrepresentation.ext
    exact Submodule.inf_orthogonal_eq_bot S.toSubmodule
  · rw [codisjoint_iff]
    apply Subrepresentation.ext
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

theorem isSemisimpleRepresentation_of_unitary
    (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho) :
    Representation.IsSemisimpleRepresentation rho :=
  ⟨fun S => ⟨orthogonalSubrepresentation rho h S,
    isCompl_orthogonalSubrepresentation rho h S⟩⟩

open scoped MonoidAlgebra

/-- Every actual finite-dimensional unitary representation has a multiplicity model. -/
def multiplicityModel (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho) :
    MultiplicityCommutant.Model ℂ[G] rho.asModule :=
  (MultiplicityCommutant.exists_representation_model rho
    (isSemisimpleRepresentation_of_unitary rho h)).some

/-- This classifies the general-linear centralizer, not yet its unitary subgroup. -/
def linearCentralizerEquiv (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho) :
    CommutantCentralizer.linearCentralizer rho ≃*
      Π c : isotypicComponents ℂ[G] rho.asModule,
        (Matrix (Fin ((multiplicityModel rho h).multiplicity c))
          (Fin ((multiplicityModel rho h).multiplicity c)) ℂ)ˣ :=
  CommutantCentralizer.linearCentralizerEquiv rho
    (isSemisimpleRepresentation_of_unitary rho h) (multiplicityModel rho h)

end

end Math.UnitaryMultiplicity
