import Physics.StandardModel.Operators.Support.Joint.SMJointAlgebraicSupport
import Math.RepresentationTheory.Characters.CompactWeylHom

/-! Joint colored occurrence from supplied color torus weights. The source
weights are constructed from the actual statistical mixed content. Only the
target's verified color/hypercharge character and the existing Weyl theorem
specialized to the Hom model are inputs; no branching or positivity is assumed. -/
namespace Physics.SMJointColoredSupport
set_option autoImplicit false
open Math Representation SMCompactTorus ComputableWeightPolynomial
open SMJointOccurrence SMJointSpinContent SU2IsotypicEvaluation
open scoped TensorProduct

def axisWeight (i : Fin 6) (a : ℤ) : Weight := Pi.single i a
def axisTerms (i : Fin 6) (m : ℕ) : Terms Weight :=
  List.ofFn (fun j : Fin (m+1) => (axisWeight i (-TauCeti.SU2.weight m j),1))
def targetTerms (colorTerms : Terms Weight) (m a b : ℕ) : Terms Weight :=
  product [axisTerms 2 m,axisTerms 3 a,axisTerms 4 b,colorTerms]
def reverseTerms (p : Terms Weight) : Terms Weight := p.map (fun x => (-x.1,x.2))
def homTerms (c : DeltaLOneSignedInput.Species → ℕ) (colorTerms : Terms Weight) (m a b : ℕ) : Terms Weight :=
  multiply (reverseTerms (SMComputableCharacter.sourceTerms c)) (targetTerms colorTerms m a b)

noncomputable section

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group := borel _
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

theorem monomial_axis (i : Fin 6) (a : ℤ) (t : Torus) :
    monomial (axisWeight i a) t = (t i : ℂ)^a := by
  simp only [monomial,axisWeight,CircleTorusCharacterLattice.torusCharacter_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem axis_evaluation (i : Fin 6) (m : ℕ) (t : Torus) :
    evaluate (fun w => monomial w t) (axisTerms i m) =
      (model m).character ((TauCeti.SU2.torusHom (t i))⁻¹) := by
  have he := congrFun (Representation.char_iso (TauCeti.SU2.symPowerModelEquiv m))
    ((TauCeti.SU2.torusHom (t i))⁻¹)
  rw [← map_inv,TauCeti.SU2.character_symPower_torusHom_zpow] at he
  change _ = (TauCeti.SU2.symPowerModel m).toRepresentation.character _
  rw [← map_inv,← he,← Fin.sum_univ_eq_sum_range]
  simp only [axisTerms,evaluate,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    Int.cast_one,one_mul,monomial_axis,TauCeti.SU2.weight]
  apply Finset.sum_congr rfl
  intro j _
  exact (zpow_neg (t i : ℂ) _).trans (inv_zpow (t i : ℂ) _).symm

private theorem comp_character {G K V : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (r : Representation ℂ G V) (phi : K →* G) (g : K) :
    Representation.character (r.comp phi) g = r.character (phi g) := rfl

private theorem external_character {G K V W : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : Representation ℂ G V) (s : Representation ℂ K W) (g : G × K) :
    (ExternalInvariantTensor.external r s).character g = r.character g.1 * s.character g.2 := by
  rw [ExternalInvariantTensor.external,Representation.char_tensor,Pi.mul_apply,
    comp_character,comp_character]
  rfl

private theorem external_continuous {G K V W : Type*} [Group G] [Group K]
    [TopologicalSpace G] [TopologicalSpace K]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (r : Representation ℂ G V) (s : Representation ℂ K W)
    (hr : ContinuousRepresentationScope.IsJointlyContinuous r)
    (hs : ContinuousRepresentationScope.IsJointlyContinuous s) :
    ContinuousRepresentationScope.IsJointlyContinuous (ExternalInvariantTensor.external r s) :=
  ContinuousUnitaryConstructions.jointlyContinuous_tprod _ _
    (hr.comp (ContinuousMonoidHom.fst G K)) (hs.comp (ContinuousMonoidHom.snd G K))

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
  (c : Representation ℂ ColorHyper B)

-- Name the intermediate analytic structures to avoid deeply nested instance
-- search; these are the existing tensor-product structures, unchanged.
local instance rightNorm (b : ℕ) : NormedAddCommGroup (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B) :=
  TensorProduct.instNormedAddCommGroup
local instance rightInner (b : ℕ) : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B) :=
  TensorProduct.instInnerProductSpace
local instance leftNorm (a b : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B)) :=
  TensorProduct.instNormedAddCommGroup
local instance leftInner (a b : ℕ) : InnerProductSpace ℂ
    (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B)) :=
  TensorProduct.instInnerProductSpace

theorem target_continuous (hc : ContinuousRepresentationScope.IsJointlyContinuous c) (m a b : ℕ) :
    ContinuousRepresentationScope.IsJointlyContinuous (target c m a b) := by
  have hright := external_continuous (model b) c (model_continuous b) hc
  have hleft := external_continuous (model a)
    ((rightTarget c b).comp rightReorder.toMonoidHom) (model_continuous a)
    (hright.comp (⟨rightReorder.toMonoidHom,continuous_swap⟩ : _ →ₜ* _))
  have hl : Continuous leftReorder := by
    change Continuous (fun g : SMJointWeakContent.Remaining => (g.2.1,(g.1,g.2.2)))
    fun_prop
  have hweak := external_continuous (model m)
    ((leftTarget c a b).comp leftReorder.toMonoidHom) (model_continuous m)
    (hleft.comp (⟨leftReorder.toMonoidHom,hl⟩ : _ →ₜ* _))
  have hw : Continuous SMJointWeakContent.reorder := by
    change Continuous (fun g : SMCombinedCompactAction.Group => (g.1.2.1,((g.1.1,g.1.2.2),g.2)))
    fun_prop
  exact hweak.comp (⟨SMJointWeakContent.reorder.toMonoidHom,hw⟩ : _ →ₜ* _)

theorem target_character (m a b : ℕ) (g : SMCombinedCompactAction.Group) :
    (target c m a b).character g = (model m).character g.1.2.1 *
      ((model a).character g.2.1 * ((model b).character g.2.2 * c.character (g.1.1,g.1.2.2))) := by
  simp only [target,weakTarget,leftTarget,rightTarget,comp_character,external_character]
  rfl

theorem target_evaluation (colorTerms : Terms Weight)
    (hc : ∀ t : Torus, evaluate (fun w => monomial w t) colorTerms =
      c.character ((SMCompactTorus.color t,t 5)⁻¹)) (m a b : ℕ) (t : Torus) :
    evaluate (fun w => monomial w t) (targetTerms colorTerms m a b) =
      (target c m a b).character ((inclusion t)⁻¹) := by
  rw [targetTerms,evaluate_product _ (SMComputableSlotWeights.monomial_zero t)
    (fun x y => SMComputableSlotWeights.monomial_add x y t)]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,axis_evaluation,hc]
  rw [target_character]
  rfl

theorem reverse_evaluation (p : Terms Weight) (t : Torus) :
    evaluate (fun w => monomial w t) (reverseTerms p) =
      evaluate (fun w => monomial w t⁻¹) p := by
  simp [reverseTerms,evaluate,SMComputableSlotWeights.monomial_inverse,List.map_map,Function.comp_def]

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev homModel (m a b : ℕ) := CompactWeylHom.model
  (V := FiniteBasisHilbertization.Copy (SMCombinedCompactContinuity.sourceBasis flavor p))
  (W := EuclideanSpace ℂ (Fin (m+1)) ⊗[ℂ]
    (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B)))
  (SMCombinedCompactContinuity.sourceModel flavor p) (target c m a b)
abbrev Input (m a b : ℕ) := CompactWeylExtraction.TorusReduction
  (homModel c flavor p m a b) inclusion.toMonoidHom monomial roots

theorem presents (hc : ContinuousRepresentationScope.IsJointlyContinuous c) (m a b : ℕ)
    (colorTerms : Terms Weight)
    (hp : ∀ t : Torus, evaluate (fun w => monomial w t) colorTerms =
      c.character ((SMCompactTorus.color t,t 5)⁻¹)) :
    CompactWeylExtraction.Presents (homModel c flavor p m a b) inclusion.toMonoidHom monomial
      (presentation (homTerms (SMIteratedContent.counts p) colorTerms m a b)) := by
  apply CompactWeylHom.presents_of_characters _ _ _ _
    (SMCombinedCompactContinuity.source_continuous flavor p) (target_continuous c hc m a b)
  intro t
  have hsource : evaluate (fun w => monomial w t)
      (reverseTerms (SMComputableCharacter.sourceTerms (SMIteratedContent.counts p))) =
      (SMCombinedCompactContinuity.sourceModel flavor p).character (inclusion t) := by
    rw [reverse_evaluation,SMComputableCharacter.source_evaluation flavor p]
    simp only [map_inv,inv_inv]
    exact congrFun (Representation.char_iso (ContinuousUnitaryConstructions.basisCopyRepresentationEquiv
      (SMCombinedCompactContinuity.sourceBasis flavor p) (SMCombinedCompactAction.source flavor p)))
      (inclusion t)
  symm
  calc
    _ = evaluate (fun w => monomial w t)
        (homTerms (SMIteratedContent.counts p) colorTerms m a b) := presentation_evaluate _ _
    _ = _ * _ := evaluate_multiply _ (fun x y => SMComputableSlotWeights.monomial_add x y t) _ _
    _ = _ := congrArg₂ (fun x y : ℂ => x*y) hsource (target_evaluation c colorTerms hp m a b t)

/-- All three SU2 labels and the entire colored target are tested together.
The right side contains no Hom or representation-equivalence proposition. -/
theorem joint_allowed_iff (hc : ContinuousRepresentationScope.IsJointlyContinuous c)
    (m : Fin (SMContentWeakBound.bound p+1))
    (a : Fin (SMChiralitySupport.count p false+1))
    (b : Fin (SMChiralitySupport.count p true+1))
    (input : Input c flavor p m.val a.val b.val) (colorTerms : Terms Weight)
    (hp : ∀ t : Torus, evaluate (fun w => monomial w t) colorTerms =
      c.character ((SMCompactTorus.color t,t 5)⁻¹)) :
    SelectionCriteria.Allowed (IntertwiningMap (jointMultiplicity flavor p m.val a.val b.val) c) ↔
      SMJointAlgebraicSupport.balance (coefficient
        (homTerms (SMIteratedContent.counts p) colorTerms m.val a.val b.val)) ≠ 0 := by
  refine (SMJointOccurrence.hom_allowed_iff c flavor p m a b).symm.trans ?_
  have he := CompactWeylHom.allowed_iff _ _ inclusion.toMonoidHom monomial roots
    (SMCombinedCompactContinuity.source_continuous flavor p)
    (target_continuous c hc m.val a.val b.val) input
    (presentation (homTerms (SMIteratedContent.counts p) colorTerms m.val a.val b.val))
    (presents c flavor p hc m.val a.val b.val colorTerms hp)
  exact he.trans (Iff.of_eq (congrArg (fun z : ℤ => z ≠ 0)
    (SMJointAlgebraicSupport.terms_balance _)))

end
end Physics.SMJointColoredSupport
