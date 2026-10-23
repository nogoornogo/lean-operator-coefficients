import Math.RepresentationTheory.Lagrangian.LagrangianInput
import Math.RepresentationTheory.Lagrangian.AllOrderDerivativeCoordinates
import Math.RepresentationTheory.Lagrangian.AllOrderSelectedCoordinates
import Math.Algebra.Jets.MixedJetMonomialBasis
import Math.Algebra.Jets.DifferentialBasisRows

/-! All-order coordinates computed from a local polynomial Lagrangian.
The row family is unbounded and has a proved full-relation span. -/
namespace Math.LocalPolynomial.Expr
set_option autoImplicit false
noncomputable section
variable {F B I H : Type*} [Group H]
  (p : Expr F B I) (rho : Representation ℂ H (A F B I))
  (stable : ∀ h, p.relations ≤ p.relations.comap (rho h))

abbrev Monomial (F B I : Type*) := MixedJetMonomialBasis.Monomial F B I
abbrev RelationRow (F B I : Type*) := DifferentialBasisRows.Row I (Monomial F B I) (Field F B)

def allOrderPresentation :
    AllOrderDerivativeCoordinates.Presentation (ι := Monomial F B I)
      (κ := RelationRow F B I) (p.input rho stable) where
  basis := MixedJetMonomialBasis.basis F B I
  relation := DifferentialBasisRows.relation D (MixedJetMonomialBasis.basis F B I) p.euler
  relation_span := DifferentialBasisRows.span_eq D _ _ MixedJetAlgebra.totalDerivative_mul

abbrev Coordinates := (p.allOrderPresentation rho stable).rows

def allOrderEquivalence : (p.input rho stable).Coefficient ≃ₗ[ℂ] p.Coordinates rho stable :=
  (p.allOrderPresentation rho stable).equivalence

theorem allOrder_reconstruction (f : (p.input rho stable).Coefficient) (u : A F B I) :
    f.val u = ((MixedJetMonomialBasis.basis F B I).repr u).sum
      (fun i a => a*(p.allOrderEquivalence rho stable f).val i) :=
  (p.allOrderPresentation rho stable).reconstruction f u

theorem allOrder_prescribed_iff (c : Monomial F B I → ℂ) :
    (∃ f : (p.input rho stable).Coefficient,
      ∀ i, f.val (MixedJetMonomialBasis.basis F B I i) = c i) ↔
    c ∈ p.Coordinates rho stable :=
  (p.allOrderPresentation rho stable).prescribed_iff c

theorem allOrder_forbidden_iff : DerivativeProhibition.Forbids (p.input rho stable) ↔
    SelectionCriteria.Forbidden (p.Coordinates rho stable) :=
  (p.allOrderPresentation rho stable).forbidden_iff

theorem allOrder_allowed_iff : DerivativeProhibition.Allows (p.input rho stable) ↔
    SelectionCriteria.Allowed (p.Coordinates rho stable) :=
  (p.allOrderPresentation rho stable).allowed_iff

def coordinateEvaluation (c : Monomial F B I → ℂ) : A F B I →ₗ[ℂ] ℂ :=
  (MixedJetMonomialBasis.basis F B I).constr ℂ c

/-- All multipliers, derivative words and group elements occur explicitly. -/
theorem coordinates_iff (c : Monomial F B I → ℂ) :
    c ∈ p.Coordinates rho stable ↔
      (∀ i j s w, coordinateEvaluation c
        (MixedJetMonomialBasis.basis F B I i * VariationalIBP.word D w (p.euler s) *
          MixedJetMonomialBasis.basis F B I j) = 0) ∧
      (∀ i j, coordinateEvaluation c (D i (MixedJetMonomialBasis.basis F B I j)) = 0) ∧
      ∀ g i, coordinateEvaluation c (rho g (MixedJetMonomialBasis.basis F B I i)) = c i := by
  change ((∀ r : RelationRow F B I, _) ∧ _) ↔ _
  constructor
  · rintro ⟨he,hg⟩
    exact ⟨fun i j s w => he (.inl (i,j,s,w)), fun i j => he (.inr (i,j)), hg⟩
  · rintro ⟨he,hd,hg⟩
    refine ⟨?_,hg⟩
    intro r
    cases r with
    | inl r => exact he r.1 r.2.1 r.2.2.1 r.2.2.2
    | inr r => exact hd r.1 r.2

/-- Target values are possible exactly when one complete coordinate family
satisfies both all-order rows and the requested evaluations. -/
theorem target_values_iff {T : Type*} (v : T → A F B I) (c : T → ℂ) :
    (∃ f : (p.input rho stable).Coefficient, ∀ t, f.val (v t) = c t) ↔
    ∃ q : p.Coordinates rho stable, ∀ t, coordinateEvaluation q.val (v t) = c t := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨p.allOrderEquivalence rho stable f,?_⟩
    intro t
    have he := congrArg (fun f : (p.input rho stable).Coefficient => f.val (v t))
      ((p.allOrderEquivalence rho stable).symm_apply_apply f)
    exact he.trans (hf t)
  · rintro ⟨q,hq⟩
    exact ⟨(p.allOrderEquivalence rho stable).symm q,hq⟩

def trivialAllOrderEquivalence :=
  p.allOrderEquivalence (Representation.trivial ℂ Unit _) (fun _ => le_refl _)

end
end Math.LocalPolynomial.Expr
