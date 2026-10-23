import Math.RepresentationTheory.Relations.FiniteLocalStatistics
import Math.RepresentationTheory.Relations.StatisticsMultiplicityCoordinates
import Math.RepresentationTheory.Coefficients.FiniteLocalRelationCompleteness
import Math.RepresentationTheory.Relations.CharacterRelationStability
import Math.RepresentationTheory.Relations.RelationStatisticsIsotypic

/-! Explicit local contraction coordinates followed by nonredundant statistics
types. Completeness and probe normalization are proved input certificates. -/
namespace Math.FiniteLocalIsotypicCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantFactorization
open scoped TensorProduct
variable {G H S A X I J : Type*} [Group G] [Group H] [Group S] [Finite S]
  [Fintype I] [DecidableEq I] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ i, f (v i) • p i)
  (ell : Representation ℂ S A) (flavor : Representation ℂ S X)
  (lc : ∀ s g u, ell s (a g u) = a g (ell s u))
  (fc : ∀ s h u, flavor s (x h u) = x h (flavor s u))

private instance cardinalNonzero : NeZero (Nat.card S : ℂ) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

abbrev statistics := FiniteLocalStatistics.statistics a p v hv hp ell flavor lc
abbrev commutes := FiniteLocalStatistics.commutes a x p v ell flavor fc

def inputCoefficientEquiv : Coefficient a x ≃ₗ[ℂ]
    IntertwiningMap (x.finsupp I) (Representation.trivial ℂ H ℂ) :=
  (FiniteInvariantFactor.equiv a x p v hv hp).trans
    (ResidualRelationPresentation.familyEquiv x)

@[simp] theorem inputCoefficientEquiv_single (f : Coefficient a x) (i : I) (u : X) :
    inputCoefficientEquiv a x p v hv hp f (Finsupp.single i u) = f (v i ⊗ₜ[ℂ] u) := by
  exact ResidualRelationPresentation.assemble_single x _ i u

omit [Finite S] in
theorem compatible (s : S) (f : Coefficient a x) :
    inputCoefficientEquiv a x p v hv hp
      (FiniteStatisticalFactor.sourceAction a x (FiniteLocalStatistics.localEquiv a ell lc)
        (FiniteLocalStatistics.flavorEquiv x flavor fc) s f) =
      (inputCoefficientEquiv a x p v hv hp f).comp
        (FiniteLocalStatistics.inputExchange a x p v ell flavor fc s) := by
  apply IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro i u
  change inputCoefficientEquiv a x p v hv hp
      (FiniteStatisticalFactor.sourceAction a x (FiniteLocalStatistics.localEquiv a ell lc)
        (FiniteLocalStatistics.flavorEquiv x flavor fc) s f) (Finsupp.single i u) =
    inputCoefficientEquiv a x p v hv hp f
      (FiniteLocalStatistics.inputMap a p v ell flavor s (Finsupp.single i u))
  rw [inputCoefficientEquiv_single]
  rw [FiniteLocalStatistics.inputMap_single, map_sum]
  simp only [inputCoefficientEquiv_single, TensorProduct.tmul_smul, map_smul]
  have hr := congrArg (fun q : Coefficient a x => q (ell s (v i) ⊗ₜ[ℂ] flavor s u))
    (FiniteInvariantFactor.reconstruction a x p v hp f)
  simpa [FiniteStatisticalFactor.sourceAction, ExternalInvariantTensor.externalEquiv,
    ExternalInvariantTensor.tensorEquiv, FiniteLocalStatistics.localEquiv,
    FiniteLocalStatistics.flavorEquiv, FiniteInvariantFactor.assemble_apply,
    rightSlice, FiniteLocalStatistics.matrix, smul_eq_mul,
    IntertwiningMap.comp, IntertwiningMap.toLinearMap_apply,
    SplitRepresentationProjection.restrictEquiv] using hr

/-- Independent finite local completeness yields a product of residual Homs
over distinct statistics types, with no flavor dimension assumption. -/
def equiv := (inputCoefficientEquiv a x p v hv hp).trans
  (CommutingStatisticsModule.coefficientEquiv (x.finsupp I)
    (statistics a p v hv hp ell flavor lc) (commutes a x p v ell flavor fc)
    (Representation.trivial ℂ H ℂ))

def statisticalEquiv (sign : S → ℂ) :=
  StatisticalCompleteness.equiv (inputCoefficientEquiv a x p v hv hp)
    (FiniteStatisticalFactor.sourceAction a x (FiniteLocalStatistics.localEquiv a ell lc)
      (FiniteLocalStatistics.flavorEquiv x flavor fc))
    (SignedRelationQuotient.action (x.finsupp I) (Representation.trivial ℂ H ℂ)
      (FiniteLocalStatistics.inputExchange a x p v ell flavor fc))
    sign (compatible a x p v hv hp ell flavor lc fc)

variable (chi : S →* ℂˣ)

abbrev relations := SignedRelationQuotient.relations (x.finsupp I)
  (FiniteLocalStatistics.inputExchange a x p v ell flavor fc) (fun s => (chi s).val)

abbrev residualQuotient := SignedRelationQuotient.quotientRepresentation (x.finsupp I)
  (FiniteLocalStatistics.inputExchange a x p v ell flavor fc) (fun s => (chi s).val)

omit [Finite S] in
/-- Statistics stability is proved for genuine character relations. -/
theorem statistics_stable : ∀ s, relations a x p v ell flavor fc chi ≤
    (relations a x p v ell flavor fc chi).comap
      (statistics a p v hv hp ell flavor lc s) :=
  CharacterRelationStability.stable (x.finsupp I) (statistics a p v hv hp ell flavor lc)
    (commutes a x p v ell flavor fc) chi

def characterQuotientEquiv :=
  (statisticalEquiv a x p v hv hp ell flavor lc fc (fun s => (chi s).val)).trans
    (SignedRelationQuotient.equiv (x.finsupp I) (Representation.trivial ℂ H ℂ)
      (FiniteLocalStatistics.inputExchange a x p v ell flavor fc) (fun s => (chi s).val))

omit [Finite S] in
@[simp] theorem extraction
    (f : StatisticalCompleteness.sector
      (FiniteStatisticalFactor.sourceAction a x (FiniteLocalStatistics.localEquiv a ell lc)
        (FiniteLocalStatistics.flavorEquiv x flavor fc)) (fun s => (chi s).val))
    (i : I) (u : X) :
    characterQuotientEquiv a x p v hv hp ell flavor lc fc chi f
      ((relations a x p v ell flavor fc chi).mkQ (Finsupp.single i u)) =
        f.val (v i ⊗ₜ[ℂ] u) := by
  exact inputCoefficientEquiv_single a x p v hv hp f.val i u

omit [Finite S] in
@[simp] theorem reconstruction
    (q : IntertwiningMap (residualQuotient a x p v ell flavor fc chi)
      (Representation.trivial ℂ H ℂ)) (u : A) (z : X) :
    ((characterQuotientEquiv a x p v hv hp ell flavor lc fc chi).symm q).val
      (u ⊗ₜ[ℂ] z) = ∑ i, p i u *
        q ((relations a x p v ell flavor fc chi).mkQ (Finsupp.single i z)) := by
  exact FiniteInvariantFactor.assemble_apply a x p _ u z

abbrev quotientStatistics := (statistics a p v hv hp ell flavor lc).quotient
  (relations a x p v ell flavor fc chi)
  (statistics_stable a x p v hv hp ell flavor lc fc chi)

omit [Finite S] in
theorem quotientCommutes : ∀ s h u,
    quotientStatistics a x p v hv hp ell flavor lc fc chi s
        (residualQuotient a x p v ell flavor fc chi h u) =
      residualQuotient a x p v ell flavor fc chi h
        (quotientStatistics a x p v hv hp ell flavor lc fc chi s u) :=
  RelationStatisticsIsotypic.quotient_commutes (x.finsupp I)
  (statistics a p v hv hp ell flavor lc) (commutes a x p v ell flavor fc)
  (relations a x p v ell flavor fc chi)
  (SignedRelationQuotient.stable (x.finsupp I)
    (FiniteLocalStatistics.inputExchange a x p v ell flavor fc) (fun s => (chi s).val))
  (statistics_stable a x p v hv hp ell flavor lc fc chi)

/-- Full signed local/flavor sector, then nonredundant residual-Hom blocks. -/
def characterIsotypicEquiv :=
  (characterQuotientEquiv a x p v hv hp ell flavor lc fc chi).trans
    (CommutingStatisticsModule.coefficientEquiv
      (residualQuotient a x p v ell flavor fc chi)
      (quotientStatistics a x p v hv hp ell flavor lc fc chi)
      (quotientCommutes a x p v hv hp ell flavor lc fc chi)
      (Representation.trivial ℂ H ℂ))

/-- The actual statistical sector in chosen simple-copy multiplicity coordinates.
Coordinate existence is proved internally, not supplied as a new hypothesis. -/
def characterMultiplicityEquiv :=
  (characterQuotientEquiv a x p v hv hp ell flavor lc fc chi).trans
    (StatisticsMultiplicityCoordinates.chosenCoefficientEquiv
      (residualQuotient a x p v ell flavor fc chi)
      (quotientStatistics a x p v hv hp ell flavor lc fc chi)
      (quotientCommutes a x p v hv hp ell flavor lc fc chi)
      (Representation.trivial ℂ H ℂ))

end
end Math.FiniteLocalIsotypicCompleteness
