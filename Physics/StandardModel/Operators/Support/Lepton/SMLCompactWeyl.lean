import Math.RepresentationTheory.SU2.SL2SymmetricSpan
import Physics.StandardModel.Operators.Support.Coordinates.SMConstantSourceCharacter
import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel

/-! Compact Weyl invariance equals full Weyl invariance for the actual constant
L statistical source, uniformly in its degree. No multiplicity input is used. -/
namespace Physics.SMLCompactWeyl
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev inclusion : WeylSpinor.Group →* NeutralHiggsPowers.G H :=
  SMWeylFiniteKernel.inclusion


theorem field_restrict :
    (DeltaLOneSignedFields.field flavor 3).comp (inclusion (H := H)) =
      ((Representation.trivial ℂ WeylSpinor.Group (Fin 2 → ℂ)).tprod
        SL2SymmetricEmbeddings.doublet).tprod
          (Representation.trivial ℂ WeylSpinor.Group (Fin 3 → ℂ)) := by
  ext g : 1
  apply TensorProduct.ext'
  intro x v
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change ((DeltaLOneSignedFields.gauge 3 1 a) ⊗ₜ[ℂ] WeylSpinor.left g b) ⊗ₜ[ℂ]
      (flavor 3 1 v) = (a ⊗ₜ[ℂ] SL2SymmetricEmbeddings.doublet g b) ⊗ₜ[ℂ] v
    rw [map_one, map_one]
    rfl
  | add x y hx hy => simp_all only [TensorProduct.add_tmul, map_add]

theorem field_spanned : SL2SymmetricSpan.Spanned
    ((DeltaLOneSignedFields.field flavor 3).comp (inclusion (H := H))) := by
  rw [field_restrict]
  exact SL2SymmetricSpan.tensor _ _
    (SL2SymmetricSpan.tensor _ _ SL2SymmetricSpan.trivial SL2SymmetricSpan.standard)
    SL2SymmetricSpan.trivial

abbrev source (n : ℕ) := PatternExteriorSource.representation
  (DeltaLOneSignedFields.field flavor) (fun _ : Fin n => (3 : DeltaLOneSignedInput.Species))

theorem source_spanned (n : ℕ) : SL2SymmetricSpan.Spanned
    ((source flavor n).comp (inclusion (H := H))) := by
  let e := SplitRepresentationProjection.restrictEquiv
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 3 n)
      (inclusion (H := H))
  apply SL2SymmetricSpan.of_surjective _ _ e.toIntertwiningMap e.surjective
  exact SL2SymmetricSpan.exterior _ (field_spanned flavor) n

theorem coefficient_fixed_iff (n : ℕ)
    (f : PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor)
      (fun _ : Fin n => (3 : DeltaLOneSignedInput.Species)) →ₗ[ℂ] ℂ) :
    (∀ g x, f (source flavor n (inclusion g) x) = f x) ↔
    (∀ u x, f (source flavor n (inclusion (SL2SymmetricEmbeddings.compactInclusion u)) x) = f x) := by
  constructor
  · intro h u x
    exact h _ x
  · exact SL2SymmetricSpan.coefficient_fixed_of_compact _ (source_spanned flavor n) f

abbrev pattern (n : ℕ) : Fin n → DeltaLOneSignedInput.Species := fun _ => 3

theorem higgs_spanned (n m : ℕ) (delta : ℤ) : SL2SymmetricSpan.Spanned
    (SMWeylFiniteKernel.action flavor (pattern n) m delta) := by
  have he : SMWeylFiniteKernel.action flavor (pattern n) m delta =
      Representation.tprod ((source flavor n).comp (inclusion (H := H)))
        (Representation.trivial ℂ WeylSpinor.Group (Sym[ℂ]^m WeakDoubletScalars.Doublet)) := by
    ext g : 1
    apply TensorProduct.ext'
    intro x y
    change (source flavor n (inclusion g) x) ⊗ₜ[ℂ]
      (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
        SMHiggsConstituents.character m delta (SMWeylFiniteKernel.inclusion g) y) = _
    exact congrArg (fun z => source flavor n (inclusion g) x ⊗ₜ[ℂ] z)
      (SMWeylFiniteKernel.boson_fixed (H := H) m delta g y)
  rw [he]
  exact SL2SymmetricSpan.tensor _ _ (source_spanned flavor n) SL2SymmetricSpan.trivial

theorem higgs_coefficient_fixed_iff (n m : ℕ) (delta : ℤ)
    (f : SMFullLocalKernel.Carrier flavor (pattern n) m →ₗ[ℂ] ℂ) :
    (∀ g x, f (SMWeylFiniteKernel.action flavor (pattern n) m delta g x) = f x) ↔
    (∀ u x, f (SMWeylFiniteKernel.action flavor (pattern n) m delta
      (SL2SymmetricEmbeddings.compactInclusion u) x) = f x) := by
  constructor
  · intro h u x
    exact h _ x
  · exact SL2SymmetricSpan.coefficient_fixed_of_compact _ (higgs_spanned flavor n m delta) f

def compactLocal : (StandardSMGaugeTensor.GaugeGroup × TauCeti.SU2) →*
    SMIntegralLocalWeights.Group :=
  MonoidHom.prodMap (MonoidHom.id _) SL2SymmetricEmbeddings.compactInclusion

/-- Equality of actual local coefficient invariance predicates, with all gauge
conditions retained; the only restricted factor is the Weyl group. -/
theorem local_coefficient_fixed_iff (n m : ℕ) (delta : ℤ)
    (f : SMFullLocalKernel.Carrier flavor (pattern n) m →ₗ[ℂ] ℂ) :
    (∀ g x, f (SMIntegralLocalWeights.action flavor (pattern n) m delta g x) = f x) ↔
    (∀ k x, f (SMIntegralLocalWeights.action flavor (pattern n) m delta (compactLocal k) x) = f x) := by
  constructor
  · intro h k x
    exact h _ x
  · intro h
    have hs := (higgs_coefficient_fixed_iff flavor n m delta f).mpr
      (fun u x => h (1,u) x)
    intro g x
    have he : g = (g.1,1) * (1,g.2) := by simp
    rw [he, map_mul, Module.End.mul_apply]
    have hg := h (g.1,1) (SMIntegralLocalWeights.action flavor (pattern n) m delta (1,g.2) x)
    have hk : compactLocal (g.1, (1 : TauCeti.SU2)) = (g.1,1) := by
      change (g.1, SL2SymmetricEmbeddings.compactInclusion 1) = (g.1,1)
      rw [map_one]
    exact (congrArg (fun k => f (SMIntegralLocalWeights.action flavor (pattern n) m delta k
      (SMIntegralLocalWeights.action flavor (pattern n) m delta (1,g.2) x))) hk).symm.trans
        (hg.trans (hs g.2 x))

abbrev compactAction (n m : ℕ) (delta : ℤ) :=
  (SMIntegralLocalWeights.action flavor (pattern n) m delta).comp compactLocal

/-- The identity on linear coefficient maps identifies the entire spaces. -/
def coefficientEquiv (n m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor (pattern n) m delta)
      ≃ₗ[ℂ] InvariantCoefficientTransport.Invariants (compactAction flavor n m delta) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' k := f.isIntertwining' (compactLocal k) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact (local_coefficient_fixed_iff flavor n m delta f.toLinearMap).mpr
          (fun k y => f.isIntertwining _ _ k y) g x }
  left_inv f := by apply IntertwiningMap.ext; rfl
  right_inv f := by apply IntertwiningMap.ext; rfl
  map_add' f g := by apply IntertwiningMap.ext; rfl
  map_smul' c f := by apply IntertwiningMap.ext; rfl

/-- Compact local coefficients map to the actual finite constraint kernel. -/
def compactKernelEquiv (n m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants (compactAction flavor n m delta) ≃ₗ[ℂ]
      SMFullLocalKernel.Kernel flavor (pattern n) m delta :=
  (coefficientEquiv flavor n m delta).symm.trans
    (SMFullLocalKernel.coefficientEquiv flavor (pattern n) m delta)

end
end Physics.SMLCompactWeyl
