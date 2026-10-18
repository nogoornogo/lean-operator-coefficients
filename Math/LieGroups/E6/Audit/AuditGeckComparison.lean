import Math.LieGroups.E6.Minuscule.GeckComparison
import Lean.Util.CollectAxioms

/-!
# E6-0d: actual Geck carriers, faithful matrices, and the numbered D5 inclusion

These examples have no supplied comparison, simplicity, dimension or descent
certificate. The complex field and pinned Dynkin data instantiate every
hypothesis. No compact-group assertion is audited by this file.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule TauCeti.DynkinType TauCeti.E6Minuscule

section OneSimpleTarget

variable {ι L₁ L₂ K : Type*} [Finite ι] [Field K] [CharZero K]
  [LieRing L₁] [LieAlgebra K L₁] [FiniteDimensional K L₁]
  [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L₂]
  [LieAlgebra.IsSimple K L₂]
  {H₁ : LieSubalgebra K L₁} {H₂ : LieSubalgebra K L₂}
  (b₁ : LieAlgebra.Basis ι H₁) (b₂ : LieAlgebra.Basis ι H₂)
  (hA : b₁.A = b₂.A)

-- No source simplicity; equal dimensions are needed only for the equivalence.
example : Function.Surjective (Math.BasedLieComparison.toSimple b₁ b₂ hA) :=
  Math.BasedLieComparison.toSimple_surjective b₁ b₂ hA

example (hd : Module.finrank K L₁ = Module.finrank K L₂) : L₁ ≃ₗ⁅K⁆ L₂ :=
  Math.BasedLieComparison.equiv b₁ b₂ hA hd

example (hd : Module.finrank K L₁ = Module.finrank K L₂) (i : ι) :
    Math.BasedLieComparison.equiv b₁ b₂ hA hd (b₁.e i) = b₂.e i :=
  Math.BasedLieComparison.equiv_e b₁ b₂ hA hd i

end OneSimpleTarget

-- The dimension wrapper retains triangularizability, not algebraic closedness.
example {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] :
    Module.finrank K L = Module.finrank K H + Nat.card H.root :=
  Math.RootSpaceDimension.finrank_eq_cartan_add_card_root H

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev E6Lie := E6.lieAlgebraBaseChange valid_E6 ℂ
abbrev D5Lie := (D 5).lieAlgebraBaseChange valid_D5 ℂ

example : Module.finrank ℂ E6Lie = 78 := PinnedGeckBasis.finrank_lieAlgebra E6 valid_E6 ℂ
example : Module.finrank ℂ D5Lie = 45 := PinnedGeckBasis.finrank_lieAlgebra (D 5) valid_D5 ℂ
example : LieAlgebra.IsSimple ℂ E6Lie := inferInstance
example : LieAlgebra.IsSimple ℂ D5Lie := inferInstance
example : matrixLieAlgebra ℂ ≃ₗ⁅ℂ⁆ E6Lie := matrixGeckEquiv ℂ
example : d5MatrixLieAlgebra ℂ ≃ₗ⁅ℂ⁆ D5Lie := d5MatrixGeckEquiv ℂ
example : Function.Injective (geckRepresentation ℂ) := geckRepresentation_injective ℂ
example : Function.Injective (geckD5Inclusion ℂ) := geckD5Inclusion_injective ℂ

example (x y : E6Lie) :
    geckRepresentation ℂ ⁅x, y⁆ = ⁅geckRepresentation ℂ x, geckRepresentation ℂ y⁆ :=
  (geckRepresentation ℂ).map_lie x y

example (i : Fin 6) :
    geckRepresentation ℂ ((PinnedGeckBasis.numberedBasis E6 valid_E6 ℂ).e i) = raising i :=
  geckRepresentation_e ℂ i

example (i : Fin 5) :
    geckD5Inclusion ℂ ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 ℂ).f i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 ℂ).f (d5Node i) :=
  geckD5Inclusion_f ℂ i

example (x : D5Lie) :
    geckRepresentation ℂ (geckD5Inclusion ℂ x) = d5GeckRepresentation ℂ x :=
  geckRepresentation_inclusion ℂ x

-- Faithfulness rules out a zero representation or a zero comparison map.
example (i : Fin E6.rank) :
    geckRepresentation ℂ ((PinnedGeckBasis.numberedBasis E6 valid_E6 ℂ).e i) ≠ 0 := by
  intro hz
  have he := (geckRepresentation_injective ℂ)
    (hz.trans (map_zero (geckRepresentation ℂ)).symm)
  exact ((PinnedGeckBasis.numberedBasis E6 valid_E6 ℂ).sl2 i).e_ne_zero he

example (i : Fin (D 5).rank) :
    geckD5Inclusion ℂ ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 ℂ).h i) ≠ 0 := by
  intro hz
  have he := (geckD5Inclusion_injective ℂ)
    (hz.trans (map_zero (geckD5Inclusion ℂ)).symm)
  exact ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 ℂ).sl2 i).h_ne_zero he

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.SerreMatrixBasis.basis,
    ``Math.SerreMatrixBasis.span_ef,
    ``Math.RootSpaceDimension.finrank_eq_cartan_add_card_root,
    ``Math.BasedLieComparison.toSimple,
    ``Math.BasedLieComparison.toSimple_surjective,
    ``Math.BasedLieComparison.equiv,
    ``Math.BasedLieComparison.equiv_h,
    ``Math.BasedLieComparison.equiv_e,
    ``Math.BasedLieComparison.equiv_f,
    ``Math.PinnedGeckBasis.numberedBasis,
    ``Math.PinnedGeckBasis.numberedBasis_A,
    ``Math.PinnedGeckBasis.finrank_lieAlgebra,
    ``Math.E6.Minuscule.e6_cartan_checked,
    ``Math.E6.Minuscule.d5_cartan_checked,
    ``Math.E6.Minuscule.d5_isSerreSystem,
    ``Math.E6.Minuscule.matrixCartan_linearIndependent,
    ``Math.E6.Minuscule.d5MatrixCartan_linearIndependent,
    ``Math.E6.Minuscule.generated_eq_matrixLieAlgebra,
    ``Math.E6.Minuscule.generated_eq_d5MatrixLieAlgebra,
    ``Math.E6.Minuscule.matrixCartanBasis,
    ``Math.E6.Minuscule.d5MatrixCartanBasis,
    ``Math.E6.Minuscule.generatedGeckEquiv,
    ``Math.E6.Minuscule.d5GeneratedGeckEquiv,
    ``Math.E6.Minuscule.matrixGeckEquiv,
    ``Math.E6.Minuscule.d5MatrixGeckEquiv,
    ``Math.E6.Minuscule.geckRepresentation,
    ``Math.E6.Minuscule.geckRepresentation_injective,
    ``Math.E6.Minuscule.geckRepresentation_h,
    ``Math.E6.Minuscule.geckRepresentation_e,
    ``Math.E6.Minuscule.geckRepresentation_f,
    ``Math.E6.Minuscule.d5GeckRepresentation,
    ``Math.E6.Minuscule.d5GeckRepresentation_injective,
    ``Math.E6.Minuscule.d5GeckRepresentation_h,
    ``Math.E6.Minuscule.d5GeckRepresentation_e,
    ``Math.E6.Minuscule.d5GeckRepresentation_f,
    ``Math.E6.Minuscule.geckD5Inclusion,
    ``Math.E6.Minuscule.geckD5Inclusion_injective,
    ``Math.E6.Minuscule.geckRepresentation_inclusion,
    ``Math.E6.Minuscule.geckD5Inclusion_h,
    ``Math.E6.Minuscule.geckD5Inclusion_e,
    ``Math.E6.Minuscule.geckD5Inclusion_f]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0d: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0d: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0d: checked {declarations.length} declarations against the standard axiom allowlist"
