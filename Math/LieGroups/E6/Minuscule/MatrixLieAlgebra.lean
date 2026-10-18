import Math.LieGroups.E6.Minuscule.LieCertificateChecks

/-!
# Dimensions of the actual generated minuscule matrix Lie algebras

The E6 simple-root matrices generate a 78-dimensional Lie subalgebra; the
retained D5 matrices generate a 45-dimensional subalgebra included in it.
These are actual matrix Lie algebras, not abstract carriers with a supplied
dimension. Comparison with Geck's algebra and compact-group identification
remain separate obligations.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open SparseMatrixCertificate MatrixLieCertificate LieData LieChecks

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [Field K]

def matrixLieAlgebra : LieSubalgebra K (Matrix (Fin 27) (Fin 27) K) :=
  LieSubalgebra.lieSpan K _ (Set.range fun i =>
    (e6GeneratorInt i).map (Int.castRingHom K))

def d5MatrixLieAlgebra : LieSubalgebra K (Matrix (Fin 27) (Fin 27) K) :=
  LieSubalgebra.lieSpan K _ (Set.range fun i =>
    (d5GeneratorInt i).map (Int.castRingHom K))

theorem matrixLieAlgebra_span :
    Submodule.span K (Set.range fun i => realize K (e6Basis i)) =
      (matrixLieAlgebra K).toSubmodule := by
  simpa only [realize, e6_actual_generators, matrixLieAlgebra] using
    span_eq_generated K e6Basis e6Generators e6Origin e6GeneratorIndex e6Closure
      e6_provenance_checked e6_generators_checked e6_closure_checked

theorem d5MatrixLieAlgebra_span :
    Submodule.span K (Set.range fun i => realize K (d5Basis i)) =
      (d5MatrixLieAlgebra K).toSubmodule := by
  simpa only [realize, d5_actual_generators, d5MatrixLieAlgebra] using
    span_eq_generated K d5Basis d5Generators d5Origin d5GeneratorIndex d5Closure
      d5_provenance_checked d5_generators_checked d5_closure_checked

theorem matrixBasis_linearIndependent [CharZero K] :
    LinearIndependent K (fun i => realize K (e6Basis i)) :=
  linearIndependent_of_pairing e6Basis e6Dual e6Scale e6_scale_nonzero e6_pairing_checked

theorem d5MatrixBasis_linearIndependent [CharZero K] :
    LinearIndependent K (fun i => realize K (d5Basis i)) :=
  linearIndependent_of_pairing d5Basis d5Dual d5Scale d5_scale_nonzero d5_pairing_checked

theorem matrixLieAlgebra_finrank [CharZero K] :
    Module.finrank K (matrixLieAlgebra K).toSubmodule = 78 := by
  have h := finrank_span_eq_card (matrixBasis_linearIndependent K)
  rw [matrixLieAlgebra_span] at h
  simpa only [Fintype.card_fin] using h

theorem d5MatrixLieAlgebra_finrank [CharZero K] :
    Module.finrank K (d5MatrixLieAlgebra K).toSubmodule = 45 := by
  have h := finrank_span_eq_card (d5MatrixBasis_linearIndependent K)
  rw [d5MatrixLieAlgebra_span] at h
  simpa only [Fintype.card_fin] using h

def d5GeneratorToE6 : Fin 10 → Fin 12 := ![5, 4, 3, 1, 2, 11, 10, 9, 7, 8]

theorem d5_generator_eq_e6 (i : Fin 10) : d5GeneratorInt i = e6GeneratorInt (d5GeneratorToE6 i) := by
  decide +kernel +revert

theorem d5MatrixLieAlgebra_le : d5MatrixLieAlgebra K ≤ matrixLieAlgebra K := by
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨i, rfl⟩
  change (d5GeneratorInt i).map (Int.castRingHom K) ∈ matrixLieAlgebra K
  rw [d5_generator_eq_e6]
  exact LieSubalgebra.subset_lieSpan (Set.mem_range_self (d5GeneratorToE6 i))

/-- Inclusion of the actual generated matrix Lie subalgebras, not a compact Spin map. -/
def d5MatrixInclusion : d5MatrixLieAlgebra K →ₗ⁅K⁆ matrixLieAlgebra K :=
  LieSubalgebra.inclusion (d5MatrixLieAlgebra_le K)

theorem d5MatrixInclusion_injective : Function.Injective (d5MatrixInclusion K) :=
  LieSubalgebra.inclusion_injective (d5MatrixLieAlgebra_le K)

end

end Math.E6.Minuscule
