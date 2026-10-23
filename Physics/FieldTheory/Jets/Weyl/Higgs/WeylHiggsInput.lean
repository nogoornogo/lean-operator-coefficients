import Physics.FieldTheory.Jets.Weyl.Equations.WeylCurrentCovariance
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Math.Algebra.Constructions.MixedScalarInclusion
import Math.RepresentationTheory.Jets.JetGradeAction

/-! One charged-lepton Weyl pair and the Higgs/dual, with their actual global
internal/Lorentz actions and all free equations in the unbounded mixed algebra. -/
namespace Physics.WeylHiggsInput
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections PairedWeylKinetic
open scoped TensorProduct
abbrev Group := HiggsStandardInput.Group

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def charge (c : Bool) : ℤ := if c then -6 else 6
def charged (c : Bool) : Representation ℂ Group (JetLinear.Field (Fin 2)) where
  toFun g := StandardSMGaugeTensor.phase (charge c) g.1 • LorentzJetIBP.weyl c g.2
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem charged_apply (c : Bool) (g : Group) : charged c g =
    StandardSMGaugeTensor.phase (charge c) g.1 • LorentzJetIBP.weyl c g.2 := rfl

theorem combined_apply {S H : Type*} [Monoid H]
    (r : Representation ℂ H (JetLinear.Field S))
    (d : Representation ℂ H (Direction (Fin 4))) (g : H) (v : Jet S (Fin 4)) :
    combined r d g v = JetLinear.map (r g) (jetMap (d g) v) := rfl

def fields : Representation ℂ Group (JetLinear.Field Label) :=
  PairedWeylInput.fieldSplit.symm.conjRingEquiv.toMonoidHom.comp
    ((charged false).prod (charged true))
abbrev directions := HiggsStandardInput.directions
def jets := combined fields directions
abbrev bosons := HiggsStandardInput.jets
def action := JetFunctor.mixedAction jets bosons
abbrev scalarEmbed : DerivativeLiteratureHiggs.A →ₐ[ℂ] A := MixedScalarInclusion.embed

theorem inc_covariant (c : Bool) (g : Group) (v : JetLinear.Field (Fin 2)) :
    fields g (PairedWeylInput.inc c v) = PairedWeylInput.inc c (charged c g v) := by
  cases c <;>
    change PairedWeylInput.fieldSplit.symm ((charged false g _), (charged true g _)) = _ <;>
    simp [PairedWeylInput.inc]

theorem jetInc_covariant (c : Bool) (g : Group) (v : Jet (Fin 2) (Fin 4)) :
    jets g (PairedWeylInput.jetInc c v) = PairedWeylInput.jetInc c
      (combined (charged c) directions g v) := by
  have he : (fields g).comp (PairedWeylInput.inc c) =
      (PairedWeylInput.inc c).comp (charged c g) := LinearMap.ext (inc_covariant c g)
  change JetLinear.map (fields g) (jetMap (directions g)
      (JetLinear.map (PairedWeylInput.inc c) v)) = _
  rw [internal_commute]
  change ((JetLinear.map (fields g)).comp (JetLinear.map (PairedWeylInput.inc c))) _ = _
  rw [← JetLinear.map_comp, he, JetLinear.map_comp]
  rfl

theorem charged_jets (c : Bool) (g : Group) (v : Jet (Fin 2) (Fin 4)) :
    combined (charged c) directions g v =
      StandardSMGaugeTensor.phase (charge c) g.1 •
        combined (LorentzJetIBP.weyl c) LorentzDirections.direction g.2 v := by
  have hm (z : ℂ) (L : JetLinear.Field (Fin 2) →ₗ[ℂ] JetLinear.Field (Fin 2)) :
      JetLinear.map (I := Fin 4) (z • L) = z • JetLinear.map L := by
    apply Finsupp.lhom_ext
    rintro ⟨a,alpha⟩ w
    simp [JetLinear.map_single, smul_smul, mul_comm]
  rw [combined_apply, charged_apply, hm]
  rfl

theorem oddInc_covariant (c : Bool) (g : Group) (v : Jet (Fin 2) (Fin 4)) :
    action g (PairedWeylInput.oddInc c v) =
      StandardSMGaugeTensor.phase (charge c) g.1 •
        PairedWeylInput.oddInc c
          (combined (LorentzJetIBP.weyl c) LorentzDirections.direction g.2 v) := by
  change ExteriorAlgebra.map (jets g) (ExteriorAlgebra.ι ℂ (PairedWeylInput.jetInc c v)) ⊗ₜ[ℂ]
    JetFunctor.polynomialMap (bosons g) 1 = _
  rw [ExteriorAlgebra.map_apply_ι, map_one, jetInc_covariant, charged_jets, map_smul]
  rw [map_smul, ← TensorProduct.smul_tmul']
  rfl

def equations : Set A := PairedWeylInput.equations ∪
  scalarEmbed '' DerivativeLiteratureHiggs.seeds 0 0

theorem scalar_equations (p : DerivativeLiteratureHiggs.A)
    (hp : p ∈ DifferentialEquation.ideal DerivativeLiteratureHiggs.D
      (DerivativeLiteratureHiggs.seeds 0 0)) :
    scalarEmbed p ∈ TwoSidedDifferential.relations D equations := by
  apply MixedScalarInclusion.equations (DerivativeLiteratureHiggs.seeds 0 0) equations
    (fun q hq => TwoSidedDifferential.seed_mem _ _ (Or.inr ⟨q,hq,rfl⟩))
  rw [TwoSidedDifferential.commutative_relations]
  exact hp

theorem derivative_covariant (g : Group) (i : Fin 4) (p : A) :
    action g (D i p) = ∑ j, (directions g (Finsupp.single i 1)) j • D j (action g p) :=
  JetFunctor.mixed_covariant jets bosons g i _
    (combined_covariant _ _ g i) (combined_covariant _ _ g i) p

theorem seed_stable (g : Group) : ∀ p ∈ equations,
    action g p ∈ TwoSidedDifferential.relations D equations := by
  rintro p ((⟨f,rfl⟩ | ⟨f,rfl⟩) | ⟨q,hq,rfl⟩)
  · change action g (PairedWeylInput.oddInc false (WeylLinearEquation.seed f)) ∈ _
    rw [oddInc_covariant, WeylLinearEquation.seed_covariant]
    exact Submodule.smul_mem _ _ (TwoSidedDifferential.seed_mem _ _
      (Or.inl (Or.inl ⟨_,rfl⟩)))
  · change action g (PairedWeylInput.oddInc true (ConjugateWeylEquation.rightSeed f)) ∈ _
    rw [oddInc_covariant, ConjugateWeylEquation.rightSeed_covariant]
    exact Submodule.smul_mem _ _ (TwoSidedDifferential.seed_mem _ _
      (Or.inl (Or.inr ⟨_,rfl⟩)))
  · change JetFunctor.mixedAction jets bosons g (MixedScalarInclusion.embed q) ∈ _
    rw [MixedScalarInclusion.natural]
    exact scalar_equations _ (HiggsStandardInput.ideal_stable 0 0 g _
      (DifferentialEquation.seed_mem _ _ hq))

theorem stable (g : Group) : TwoSidedDifferential.combined D equations ≤
    (TwoSidedDifferential.combined D equations).comap (action g) :=
  TwoSidedCovariance.combined_stable D equations (action g)
    (JetFunctor.mixedAction_mul jets bosons g) _ (derivative_covariant g) (seed_stable g)

def input : DerivativeInterface.Input Group A where
  action := action
  relations := TwoSidedDifferential.combined D equations
  stable := stable

abbrev V := MixedJetAlgebra.grade Label Label (Fin 4) 2 4 1
theorem grade_stable (g : Group) : V ≤ V.comap (action g) :=
  fun _ hp => JetFunctor.mixedAction_mem jets bosons (combined_order fields directions)
    (combined_order HiggsStandardInput.fields directions) g hp
def selected := input.select V grade_stable

end
end Physics.WeylHiggsInput
