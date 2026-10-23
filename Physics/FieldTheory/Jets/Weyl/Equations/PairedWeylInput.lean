import Math.Algebra.Constructions.PairedWeylKinetic
import Math.RepresentationTheory.Constructions.PairedComponentFields
import Math.RepresentationTheory.Invariants.TwoSidedCovariance
import Physics.FieldTheory.Jets.Weyl.Equations.ConjugateWeylEquation
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureMixed

/-! Both physical Weyl equations in the full mixed algebra with off-shell
Higgs component spectators. Lorentz symmetry is actual SL(2,C). -/
namespace Physics.PairedWeylInput
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections PairedWeylKinetic
open scoped TensorProduct
abbrev Group := LorentzDirections.Group
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def fieldSplit : JetLinear.Field Label ≃ₗ[ℂ] JetLinear.Field (Fin 2) × JetLinear.Field (Fin 2) :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ Label).trans
    (PairedComponentFields.split.trans
      (LorentzJetIBP.spinorBasis.symm.prodCongr LorentzJetIBP.spinorBasis.symm))
def fields : Representation ℂ Group (JetLinear.Field Label) :=
  fieldSplit.symm.conjRingEquiv.toMonoidHom.comp
    ((LorentzJetIBP.weyl false).prod (LorentzJetIBP.weyl true))
def inc (c : Bool) : JetLinear.Field (Fin 2) →ₗ[ℂ] JetLinear.Field Label :=
  fieldSplit.symm.toLinearMap.comp (if c then LinearMap.inr ℂ _ _ else LinearMap.inl ℂ _ _)

theorem inc_single (c : Bool) (a : Fin 2) (z : ℂ) :
    inc c (Finsupp.single a z) = Finsupp.single (c,a) z := by
  apply fieldSplit.injective
  cases c <;>
    simp [inc,fieldSplit,PairedComponentFields.split,LorentzJetIBP.spinorBasis,
      Pi.single_apply]

theorem inc_covariant (c : Bool) (g : Group) (v : JetLinear.Field (Fin 2)) :
    fields g (inc c v) = inc c (LorentzJetIBP.weyl c g v) := by
  cases c <;>
    change fieldSplit.symm ((LorentzJetIBP.weyl false g _),
      (LorentzJetIBP.weyl true g _)) = _ <;>
    simp [inc]

def jetInc (c : Bool) : Jet (Fin 2) (Fin 4) →ₗ[ℂ] Jet Label (Fin 4) := JetLinear.map (inc c)
def jets := combined fields LorentzDirections.direction
def bosons := combined (Representation.trivial ℂ Group (JetLinear.Field Label)) LorentzDirections.direction
def action := JetFunctor.mixedAction jets bosons
def oddInc (c : Bool) : Jet (Fin 2) (Fin 4) →ₗ[ℂ] A :=
  JetFunctor.oddVector.comp (jetInc c)

theorem jetInc_single (c : Bool) (a : Fin 2) (alpha : Fin 4 →₀ ℕ) (z : ℂ) :
    jetInc c (Finsupp.single (a,alpha) z) = Finsupp.single ((c,a),alpha) z := by
  simp [jetInc,inc_single]

theorem jetInc_covariant (c : Bool) (g : Group) (v : Jet (Fin 2) (Fin 4)) :
    jets g (jetInc c v) = jetInc c (combined (LorentzJetIBP.weyl c) LorentzDirections.direction g v) := by
  have he : (fields g).comp (inc c) = (inc c).comp (LorentzJetIBP.weyl c g) :=
    LinearMap.ext (inc_covariant c g)
  change JetLinear.map (fields g) (jetMap (LorentzDirections.direction g) (JetLinear.map (inc c) v)) = _
  rw [internal_commute]
  change ((JetLinear.map (fields g)).comp (JetLinear.map (inc c))) _ = _
  rw [← JetLinear.map_comp,he,JetLinear.map_comp]
  rfl

theorem oddVector_covariant (g : Group) (v : Jet Label (Fin 4)) :
    action g (JetFunctor.oddVector v) = JetFunctor.oddVector (jets g v) := by
  change ExteriorAlgebra.map (jets g) (ExteriorAlgebra.ι ℂ v) ⊗ₜ[ℂ]
    JetFunctor.polynomialMap (bosons g) 1 = _
  rw [ExteriorAlgebra.map_apply_ι,map_one]
  rfl

theorem oddInc_covariant (c : Bool) (g : Group) (v : Jet (Fin 2) (Fin 4)) :
    action g (oddInc c v) = oddInc c
      (combined (LorentzJetIBP.weyl c) LorentzDirections.direction g v) := by
  change action g (JetFunctor.oddVector (jetInc c v)) = _
  rw [oddVector_covariant,jetInc_covariant]
  rfl

def leftSeed : WeylLinearEquation.Equations →ₗ[ℂ] A :=
  (oddInc false).comp WeylLinearEquation.seed
def rightSeed : WeylLinearEquation.Equations →ₗ[ℂ] A :=
  (oddInc true).comp ConjugateWeylEquation.rightSeed
def equations : Set A := Set.range leftSeed ∪ Set.range rightSeed

theorem left_covariant (g : Group) (f : WeylLinearEquation.Equations) :
    action g (leftSeed f) = leftSeed (WeylSpinor.right.dual g f) := by
  change action g (oddInc false (WeylLinearEquation.seed f)) = _
  rw [oddInc_covariant,WeylLinearEquation.seed_covariant]
  rfl
theorem right_covariant (g : Group) (f : WeylLinearEquation.Equations) :
    action g (rightSeed f) = rightSeed (WeylSpinor.left.dual g f) := by
  change action g (oddInc true (ConjugateWeylEquation.rightSeed f)) = _
  rw [oddInc_covariant,ConjugateWeylEquation.rightSeed_covariant]
  rfl

theorem derivative_covariant (g : Group) (i : Fin 4) (p : A) :
    action g (D i p) = ∑ j, (LorentzDirections.direction g (Finsupp.single i 1)) j •
      D j (action g p) :=
  JetFunctor.mixed_covariant jets bosons g i _
    (combined_covariant _ _ g i) (combined_covariant _ _ g i) p

theorem stable (g : Group) : TwoSidedDifferential.combined D equations ≤
    (TwoSidedDifferential.combined D equations).comap (action g) := by
  apply TwoSidedCovariance.combined_stable D equations (action g)
    (JetFunctor.mixedAction_mul jets bosons g) _ (derivative_covariant g)
  rintro p (⟨f,rfl⟩ | ⟨f,rfl⟩)
  · rw [left_covariant]
    exact TwoSidedDifferential.seed_mem _ _ (Or.inl ⟨_,rfl⟩)
  · rw [right_covariant]
    exact TwoSidedDifferential.seed_mem _ _ (Or.inr ⟨_,rfl⟩)

def direct : DerivativeInterface.Input Group A where
  action := action
  relations := TwoSidedDifferential.combined D equations
  stable := stable

end
end Physics.PairedWeylInput
