import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneFamilyCompleteness
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneConjugation

open Math

/-!
# Dimension-six Delta L one coefficient completeness

The input is the independently defined degree-one invariant exterior sector on
all ten signed SM field species. The four factors below have only residual
symmetry and the already proved flavor exchange conditions; gauge and Lorentz
invariance are not hypotheses on these output coordinates.
-/
namespace Physics.DeltaLOneCoefficientCompleteness
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneSignedFields
open DeltaLOneFourFamilyDecomposition DeltaLOneFamilyCompleteness
variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

abbrev ResidualProduct :=
  DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3) ×
    (QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4) ×
      (QqqlExchange.residualSpace (flavor 0) (flavor 3) ×
        DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4)))

def familyProduct : (∀ i : Fin 4, FamilySector flavor i) ≃ₗ[ℂ]
    FamilySector flavor 0 × (FamilySector flavor 1 ×
      (FamilySector flavor 2 × FamilySector flavor 3)) where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2.1
    | 2 => f.2.2.1
    | 3 => f.2.2.2
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Complete extraction and reconstruction, with arbitrary supplied residual
group and multiplicity representations and no finite-dimensionality assumption. -/
def equiv : Sector flavor 1 ≃ₗ[ℂ] ResidualProduct flavor :=
  (DeltaLOneFourFamilyDecomposition.equiv flavor).trans
    ((familyProduct flavor).trans
      (LinearEquiv.prodCongr (duqlEquiv flavor)
        (LinearEquiv.prodCongr (qqueEquiv flavor)
          (LinearEquiv.prodCongr (qqqlEquiv flavor) (duueEquiv flavor)))))

def extract := (equiv flavor).toLinearMap
def reconstruct := (equiv flavor).symm.toLinearMap

/-- The common statistics proofs leave the complete four-family extraction
in its original physical order and normalization. -/
theorem extract_factorization (f : Sector flavor 1) : extract flavor f =
    (duqlEquiv flavor (DeltaLOneFourFamilyDecomposition.equiv flavor f 0),
      qqueEquiv flavor (DeltaLOneFourFamilyDecomposition.equiv flavor f 1),
      qqqlEquiv flavor (DeltaLOneFourFamilyDecomposition.equiv flavor f 2),
      duueEquiv flavor (DeltaLOneFourFamilyDecomposition.equiv flavor f 3)) := rfl

theorem reconstruct_factorization (k : ResidualProduct flavor) : reconstruct flavor k =
    (DeltaLOneFourFamilyDecomposition.equiv flavor).symm
      ((familyProduct flavor).symm ((duqlEquiv flavor).symm k.1,
        (qqueEquiv flavor).symm k.2.1, (qqqlEquiv flavor).symm k.2.2.1,
        (duueEquiv flavor).symm k.2.2.2)) := rfl

@[simp] theorem reconstruct_extract (f : Sector flavor 1) :
    reconstruct flavor (extract flavor f) = f := (equiv flavor).symm_apply_apply f

@[simp] theorem extract_reconstruct (k : ResidualProduct flavor) :
    extract flavor (reconstruct flavor k) = k := (equiv flavor).apply_symm_apply k

theorem extract_injective : Function.Injective (extract flavor) := (equiv flavor).injective
theorem reconstruct_surjective : Function.Surjective (reconstruct flavor) :=
  (equiv flavor).symm.surjective

theorem coefficient_ext (f g : Sector flavor 1)
    (h : extract flavor f = extract flavor g) : f = g := extract_injective flavor h

theorem nonzero_coordinates_iff : (∃ f : Sector flavor 1, f ≠ 0) ↔
    ∃ k : ResidualProduct flavor, k ≠ 0 :=
  ConstrainedCompleteness.exists_nonzero_iff (equiv flavor)

/-- Nonzero refers to an allowed coefficient, not a UV-generated Wilson coefficient. -/
theorem nonzero_iff : (∃ f : Sector flavor 1, f ≠ 0) ↔
    (∃ k : DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3), k ≠ 0) ∨
    (∃ k : QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4), k ≠ 0) ∨
    (∃ k : QqqlExchange.residualSpace (flavor 0) (flavor 3), k ≠ 0) ∨
    (∃ k : DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4), k ≠ 0) := by
  constructor
  · rintro ⟨f,hf⟩
    have hk : extract flavor f ≠ 0 := by
      intro h
      apply hf
      apply extract_injective flavor
      simpa using h
    by_contra hn
    push Not at hn
    apply hk
    exact Prod.ext (hn.1 _) (Prod.ext (hn.2.1 _)
      (Prod.ext (hn.2.2.1 _) (hn.2.2.2 _)))
  · intro h
    have hex : ∃ k : ResidualProduct flavor, k ≠ 0 := by
      rcases h with ⟨k,hk⟩ | ⟨k,hk⟩ | ⟨k,hk⟩ | ⟨k,hk⟩
      · exact ⟨(k,0,0,0), fun h => hk (congrArg Prod.fst h)⟩
      · exact ⟨(0,k,0,0), fun h => hk (congrArg (fun v => v.2.1) h)⟩
      · exact ⟨(0,0,k,0), fun h => hk (congrArg (fun v => v.2.2.1) h)⟩
      · exact ⟨(0,0,0,k), fun h => hk (congrArg (fun v => v.2.2.2) h)⟩
    obtain ⟨k,hk⟩ := hex
    refine ⟨reconstruct flavor k, ?_⟩
    intro h
    apply hk
    have he := congrArg (extract flavor) h
    simpa using he

/-- Negative degree has the same coordinate description semilinearly, provided
the model supplies an equivariant species-reversing field involution. -/
def negativeEquiv
    (c : (∀ s, Field (F := F) s) ≃ₛₗ[starRingEnd ℂ] (∀ s, Field (F := F) s))
    (hc : ∀ g x, c (FiniteSpeciesExterior.representation (field flavor) g x) =
      FiniteSpeciesExterior.representation (field flavor) g (c x))
    (hi : ∀ x, c (c x) = x)
    (hs : ∀ s (x : Field (F := F) s), c (Pi.single s x) =
      Pi.single (DeltaLOneConjugation.conjugateSpecies s)
        (c (Pi.single s x) (DeltaLOneConjugation.conjugateSpecies s))) :
    Sector flavor (-1) ≃ₛₗ[starRingEnd ℂ] ResidualProduct flavor :=
  (DeltaLOneConjugation.equiv (field flavor) c hc hi hs 1).symm.trans (equiv flavor)

end
end Physics.DeltaLOneCoefficientCompleteness
