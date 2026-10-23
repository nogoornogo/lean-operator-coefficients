import Physics.FieldTheory.Spinor.Weyl.WeylIndependentAction
import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel
import Math.RepresentationTheory.Relations.BiaffineStatisticalOrbits
import Math.RepresentationTheory.SU2.SL2StatisticalSpan
import Math.RepresentationTheory.Relations.StatisticalSourceRestriction
import Math.RepresentationTheory.SU2.SL2PairCompactComparison

/-! Mixed-chirality source comparison with independent compact Weyl factors. -/
namespace Physics.SMMixedCompactWeyl
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
abbrev Pair := WeylIndependentAction.Group
abbrev paired := WeylIndependentAction.paired

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def field (s : DeltaLOneSignedInput.Species) : Representation ℂ Pair
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  ((Representation.trivial ℂ Pair (DeltaLOneSignedFields.GaugeCarrier s)).tprod
    (WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s))).tprod
      (Representation.trivial ℂ Pair (ThreeGenerationFermionBound.Flavor s))

theorem field_paired (s : DeltaLOneSignedInput.Species) :
    (field s).comp paired = (DeltaLOneSignedFields.field flavor s).comp SMWeylFiniteKernel.inclusion := by
  ext g : 1
  apply TensorProduct.ext'
  intro x y
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change (a ⊗ₜ[ℂ] WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s) (paired g) b) ⊗ₜ[ℂ] y =
      (DeltaLOneSignedFields.gauge s 1 a ⊗ₜ[ℂ]
        FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded s) g b) ⊗ₜ[ℂ] flavor s 1 y
    rw [map_one,map_one]
    exact congrArg (fun z => (a ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] y)
      (LinearMap.congr_fun (congrArg (fun rho => rho g) (WeylIndependentAction.spin_paired _)) b)
  | add x y hx hy => simp_all only [TensorProduct.add_tmul,map_add]

def direction (s : DeltaLOneSignedInput.Species) (a : WeylRealTransvections.Pair) :
    Module.End ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  TensorProduct.map (TensorProduct.map LinearMap.id (WeylIndependentAction.direction a)) LinearMap.id

theorem field_affine (s : DeltaLOneSignedInput.Species) (a : WeylRealTransvections.Pair)
    (u v : ℂ) (x : DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :
    field s (WeylIndependentAction.family a u,WeylIndependentAction.family a v) x =
      x + (if DeltaLOneSignedFields.rightHanded s then v else u) • direction s a x := by
  have he : field s (WeylIndependentAction.family a u,WeylIndependentAction.family a v) =
      LinearMap.id + (if DeltaLOneSignedFields.rightHanded s then v else u) • direction s a := by
    ext x y z
    cases h : DeltaLOneSignedFields.rightHanded s <;>
      simp [field,direction,Representation.tprod_apply,WeylIndependentAction.spin_affine,h,
      TensorProduct.tmul_add,TensorProduct.tmul_smul,TensorProduct.add_tmul,TensorProduct.smul_tmul']
  exact LinearMap.congr_fun he x

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def source : Representation ℂ Pair
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :=
  PatternExteriorSource.representation field p

theorem source_polynomial : PairedPolynomialInvariants.PolynomialOrbits (source flavor p)
    WeylIndependentAction.family := by
  apply BiaffineStatisticalOrbits.descend _ _ _ (PatternExteriorSource.onto field p)
    (PatternExteriorSource.onto_surjective field p)
  exact BiaffineStatisticalOrbits.raw_polynomial _ _
    (fun i => DeltaLOneSignedFields.rightHanded (p i))
    (fun a i x => ⟨direction (p i) a x, fun u v => field_affine (p i) a u v x⟩)

theorem source_paired : (source flavor p).comp paired = SMWeylFiniteKernel.source flavor p := by
  let a := fun s => (DeltaLOneSignedFields.field flavor s).comp SMWeylFiniteKernel.inclusion
  have h₁ := StatisticalSourceRestriction.source field paired a p (field_paired flavor)
  have h₂ := StatisticalSourceRestriction.source (DeltaLOneSignedFields.field flavor)
    SMWeylFiniteKernel.inclusion a p (fun _ => rfl)
  exact h₁.trans h₂.symm

def branch (right : Bool) : WeylSpinor.Group →* Pair :=
  if right then MonoidHom.inr _ _ else MonoidHom.inl _ _

theorem spin_branch (right side : Bool) : (WeylIndependentAction.spin right).comp (branch side) =
    if right = side then SL2SymmetricEmbeddings.doublet
      else Representation.trivial ℂ WeylSpinor.Group WeylSpinor.Space := by
  cases right <;> cases side <;>
    simp only [WeylIndependentAction.spin,branch,Bool.false_eq_true,reduceIte]
  all_goals ext g x : 2
  all_goals simp [SL2SymmetricEmbeddings.doublet, WeylSpinor.left,Representation.trivial]
  all_goals rfl

theorem field_spanned (s : DeltaLOneSignedInput.Species) (side : Bool) :
    SL2SymmetricSpan.Spanned ((field s).comp (branch side)) := by
  have he : (field s).comp (branch side) =
      ((Representation.trivial ℂ WeylSpinor.Group (DeltaLOneSignedFields.GaugeCarrier s)).tprod
        ((WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)).comp (branch side))).tprod
          (Representation.trivial ℂ WeylSpinor.Group (ThreeGenerationFermionBound.Flavor s)) := rfl
  rw [he,spin_branch]
  split_ifs
  · exact SL2SymmetricSpan.tensor _ _
      (SL2SymmetricSpan.tensor _ _ SL2SymmetricSpan.trivial SL2SymmetricSpan.standard)
      SL2SymmetricSpan.trivial
  · exact SL2SymmetricSpan.tensor _ _
      (SL2SymmetricSpan.tensor _ _ SL2SymmetricSpan.trivial SL2SymmetricSpan.trivial)
      SL2SymmetricSpan.trivial

theorem source_spanned (side : Bool) : SL2SymmetricSpan.Spanned ((source flavor p).comp (branch side)) := by
  let a := PatternExteriorSource.representation (fun s => (field s).comp (branch side)) p
  let e : Representation.Equiv a ((source flavor p).comp (branch side)) :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨x.val,x.property⟩
          invFun := fun x => ⟨x.val,x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' g := rfl }
  exact SL2SymmetricSpan.of_surjective a _ e.toIntertwiningMap e.surjective
    (SL2StatisticalSpan.source _ p (fun s => field_spanned s side))

abbrev Carrier (m : ℕ) := SMFullLocalKernel.Carrier flavor p m

def action (m : ℕ) : Representation ℂ Pair (Carrier flavor p m) :=
  (source flavor p).tprod (Representation.trivial ℂ Pair (Sym[ℂ]^m WeakDoubletScalars.Doublet))

theorem action_polynomial (m : ℕ) : PairedPolynomialInvariants.PolynomialOrbits
    (action flavor p m) WeylIndependentAction.family :=
  BiaffineStatisticalOrbits.tensor_fixed _ _ _ (source_polynomial flavor p)
    (by intro a u v y; rfl)

theorem action_spanned (m : ℕ) (side : Bool) :
    SL2SymmetricSpan.Spanned ((action flavor p m).comp (branch side)) := by
  have he := StatisticalSourceRestriction.tensor (branch side) (source flavor p)
    (Representation.trivial ℂ Pair (Sym[ℂ]^m WeakDoubletScalars.Doublet))
    ((source flavor p).comp (branch side))
    (Representation.trivial ℂ WeylSpinor.Group (Sym[ℂ]^m WeakDoubletScalars.Doublet)) rfl rfl
  unfold action
  rw [he]
  exact SL2SymmetricSpan.tensor _ _ (source_spanned flavor p side) SL2SymmetricSpan.trivial

theorem action_paired (m : ℕ) (delta : ℤ) :
    (action flavor p m).comp paired = SMWeylFiniteKernel.action flavor p m delta := by
  let b := Representation.trivial ℂ WeylSpinor.Group (Sym[ℂ]^m WeakDoubletScalars.Doublet)
  have hb : (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta).comp SMWeylFiniteKernel.inclusion = b := by
    ext g : 1
    apply LinearMap.ext
    intro y
    exact SMWeylFiniteKernel.boson_fixed m delta g y
  have h₁ := StatisticalSourceRestriction.tensor paired (source flavor p)
    (Representation.trivial ℂ Pair (Sym[ℂ]^m WeakDoubletScalars.Doublet))
    (SMWeylFiniteKernel.source flavor p) b (source_paired flavor p) rfl
  have h₂ := StatisticalSourceRestriction.tensor (SMWeylFiniteKernel.inclusion (H := H))
    (SMFiniteHiggsSupport.source flavor p)
    (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta) (SMWeylFiniteKernel.source flavor p) b rfl hb
  exact h₁.trans h₂.symm

def compact : (TauCeti.SU2 × TauCeti.SU2) →* Pair :=
  MonoidHom.prodMap SL2SymmetricEmbeddings.compactInclusion SL2SymmetricEmbeddings.compactInclusion

theorem coefficient_fixed_iff (m : ℕ) (delta : ℤ) (f : Carrier flavor p m →ₗ[ℂ] ℂ) :
    (∀ g x, f (SMWeylFiniteKernel.action flavor p m delta g x) = f x) ↔
      ∀ u x, f (action flavor p m (compact u) x) = f x := by
  have hsep := PairedPolynomialInvariants.fixed_iff_action (action flavor p m) WeylSpinor.conjugate
    WeylIndependentAction.family WeylIndependentAction.family_generates
    WeylIndependentAction.family_conjugate WeylIndependentAction.family_zero (action_polynomial flavor p m)
    (SMWeylFiniteKernel.action flavor p m delta) (action_paired flavor p m delta) f
  exact hsep.trans (SL2PairCompactComparison.fixed_iff (action flavor p m)
    (action_spanned flavor p m false) (action_spanned flavor p m true) f)

end
end Physics.SMMixedCompactWeyl
