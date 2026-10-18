import Physics.StandardModel.Operators.WeinbergPermutationCompleteness
import Physics.StandardModel.Operators.WeinbergModelSector
import Math.RepresentationTheory.FiniteLocalRelationCompleteness

open Math

/-! The general finite-local relation quotient specializes to the independently
defined Weinberg fermion sector. This is an actual consumer of local weak/Weyl
completeness, not an assumed relation-space classification. -/
namespace GUT.WeinbergRelationCompleteness
set_option autoImplicit false
noncomputable section
open Representation WeinbergResidualHom
open scoped TensorProduct

def contractions (_ : Unit) := localContraction
def probes (_ : Unit) := localWitness

theorem normalized (i j : Unit) : contractions i (probes j) = if i = j then 1 else 0 := by
  simp [contractions, probes]

theorem complete (f : IntertwiningMap localRepresentation
    (Representation.trivial ℂ _ ℂ)) : f = ∑ i : Unit, f (probes i) • contractions i := by
  rw [Fintype.sum_unique]
  exact local_unique f

variable {H F : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ H F)

abbrev localExchange (_ : Unit) := WeinbergPermutationCompleteness.localSwap
abbrev flavorExchange (_ : Unit) := Representation.TensorProduct.comm a a
abbrev sign (_ : Unit) : ℂ := -1

abbrev relations := FiniteLocalRelationCompleteness.relations
  localRepresentation (a.tprod a) contractions probes localExchange (flavorExchange a) sign

abbrev residualRepresentation := FiniteLocalRelationCompleteness.residualRepresentation
  localRepresentation (a.tprod a) contractions probes localExchange (flavorExchange a) sign

def generatorEquiv : sector a ≃ₗ[ℂ] StatisticalCompleteness.sector
    (FiniteStatisticalFactor.sourceAction localRepresentation (a.tprod a)
      localExchange (flavorExchange a)) sign :=
  (ConstrainedCompleteness.Presentation.mk (LinearEquiv.refl ℂ _)
    (fun f => (WeinbergPermutationCompleteness.source_sector_iff a f).symm)).equiv

/-- The Weinberg coefficient space is the residual Hom out of the explicit
input-relation quotient supplied by the general theorem. -/
def equiv : sector a ≃ₗ[ℂ]
    IntertwiningMap (residualRepresentation a) (Representation.trivial ℂ H ℂ) :=
  (generatorEquiv a).trans
    (FiniteLocalRelationCompleteness.equiv localRepresentation (a.tprod a)
      contractions probes normalized complete localExchange (flavorExchange a) sign)

@[simp] theorem extraction (f : sector a) (w : F ⊗[ℂ] F) :
    equiv a f ((relations a).mkQ (Finsupp.single () w)) =
      f.val (localWitness ⊗ₜ[ℂ] w) := by
  exact FiniteLocalRelationCompleteness.extraction localRepresentation (a.tprod a)
    contractions probes normalized complete localExchange (flavorExchange a) sign
    (generatorEquiv a f) () w

/-- Comparison is a proved equivalence of Hom spaces, not an asserted identity
of the Finsupp quotient carrier with the symmetric-power carrier. -/
def symmetricHomEquiv :
    IntertwiningMap (residualRepresentation a) (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ H ℂ) :=
  (equiv a).symm.trans (WeinbergPermutationCompleteness.homEquiv a)

@[simp] theorem symmetricHomEquiv_agrees (f : sector a) :
    symmetricHomEquiv a (equiv a f) = WeinbergResidualHom.homEquiv a f := by
  simp only [symmetricHomEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    WeinbergPermutationCompleteness.homEquiv_agrees]

/-- The independent physical exterior/symmetric realization is transported
before applying the general quotient construction. -/
def modelEquiv : WeinbergModelSector.ModelSector a ≃ₗ[ℂ]
    IntertwiningMap (residualRepresentation a) (Representation.trivial ℂ H ℂ) :=
  (WeinbergModelSector.sectorEquiv a).trans (equiv a)

@[simp] theorem modelEquiv_agrees (f : WeinbergModelSector.ModelSector a) :
    symmetricHomEquiv a (modelEquiv a f) = WeinbergModelSector.homEquiv a f := by
  change symmetricHomEquiv a (equiv a (WeinbergModelSector.sectorEquiv a f)) = _
  rw [symmetricHomEquiv_agrees]
  exact congrArg (fun e => e (WeinbergModelSector.sectorEquiv a f))
    (WeinbergPermutationCompleteness.homEquiv_agrees a).symm

end
end GUT.WeinbergRelationCompleteness
