import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoModelInterface
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor

open Math

/-! Tensor-order and physical-action bridge for residual multiplicities. -/
namespace Physics.DeltaBTwoFlavorBridge
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkFlavorCoordinates DeltaBTwoModelInterface
open scoped TensorProduct

variable {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]

def reorder : ((SMEpsilonTensor.Color ⊗[ℂ] V) ⊗[ℂ] Spin) ≃ₗ[ℂ] (Quark ⊗[ℂ] V) :=
  (TensorProduct.assoc ℂ _ _ _).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ _) (TensorProduct.comm ℂ V Spin)).trans
      (TensorProduct.assoc ℂ SMEpsilonTensor.Color Spin V).symm)

@[simp] theorem reorder_tmul (c : SMEpsilonTensor.Color) (v : V) (s : Spin) :
    reorder ((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) = (c ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] v := by
  simp [reorder]

def model (r : Representation ℂ H V) (y : ℤ) :
    Representation ℂ (SymmetryGroup H) ((SMEpsilonTensor.Color ⊗[ℂ] V) ⊗[ℂ] Spin) :=
  ExternalInvariantTensor.external
    (ExternalInvariantTensor.external (StandardSMGaugeTensor.twist StandardSMGaugeTensor.color y) r)
    WeylSpinor.right

/-- Transported action: hypercharge phase, color/Weyl action and residual action.
The weak factor acts trivially on these right-handed fields. -/
theorem reorder_action (r : Representation ℂ H V) (y : ℤ) (g : SymmetryGroup H)
    (v : (SMEpsilonTensor.Color ⊗[ℂ] V) ⊗[ℂ] Spin) :
    reorder (model r y g v) = StandardSMGaugeTensor.phase y g.1.1 •
      TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (r g.1.2)
        (reorder v) := by
  have he : reorder.toLinearMap.comp (model r y g) =
      StandardSMGaugeTensor.phase y g.1.1 •
        (TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (r g.1.2)).comp
          reorder.toLinearMap := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    ext c t s
    simp [model, ExternalInvariantTensor.external, StandardSMGaugeTensor.twist,
      StandardSMGaugeTensor.color, colorAction, spinAction, SmallSpecialUnitary.defining,
      TensorProduct.smul_tmul']
  exact DFunLike.congr_fun he v

theorem reorder_up_action (r : Representation ℂ H V) (g : SymmetryGroup H)
    (v : (SMEpsilonTensor.Color ⊗[ℂ] V) ⊗[ℂ] Spin) :
    reorder (upModel r g v) = StandardSMGaugeTensor.phase 4 g.1.1 •
      TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (r g.1.2)
        (reorder v) := reorder_action r 4 g v

theorem reorder_down_action (r : Representation ℂ H V) (g : SymmetryGroup H)
    (v : (SMEpsilonTensor.Color ⊗[ℂ] V) ⊗[ℂ] Spin) :
    reorder (downModel r g v) = StandardSMGaugeTensor.phase (-2) g.1.1 •
      TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (r g.1.2)
        (reorder v) := reorder_action r (-2) g v

universe u
variable {U D : Type u} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D]
  (up : Representation ℂ H U) (down : Representation ℂ H D)

def charge (i : Fin 6) : ℤ := if i = 0 ∨ i = 2 then 4 else -2

def slotAction (g : SymmetryGroup H) (i : Fin 6) :
    Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i →ₗ[ℂ]
      Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i :=
  StandardSMGaugeTensor.phase (charge i) g.1.1 •
    TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2))
      (SixQuarkTypedFlavor.slotRepresentation U D up down i g.1.2)

def IsPhysicalInvariant (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D)) : Prop :=
  ∀ g v, f (fun i => slotAction up down g i (v i)) = f v

theorem phase_product (g : StandardSMGaugeTensor.GaugeGroup) :
    (∏ i : Fin 6, StandardSMGaugeTensor.phase (charge i) g) = 1 := by
  simpa [charge, Fin.prod_univ_succ, mul_assoc] using DeltaBTwoSixQuark.sixQuark_phases g

private theorem split_action (c : SixColorInvariant.Group) (s : WeylSpinor.Group)
    (a : V →ₗ[ℂ] V) :
    TensorProduct.map ((colorAction c).comp (spinAction s)) a =
      (TensorProduct.map (colorAction c) (LinearMap.id : V →ₗ[ℂ] V)).comp
        ((TensorProduct.map (spinAction s) (LinearMap.id : V →ₗ[ℂ] V)).comp
          (TensorProduct.map LinearMap.id a)) := by
  apply TensorProduct.ext
  ext q t
  simp

/-- Full physical invariance follows from the independently classified actions;
hypercharge cancels rather than being omitted from the model. -/
theorem physical_invariant (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D))
    (hf : IsInvariant f)
    (hr : IsResidualInvariant (SixQuarkTypedFlavor.slotRepresentation U D up down) f) :
    IsPhysicalInvariant up down f := by
  intro g v
  change f (fun i => StandardSMGaugeTensor.phase (charge i) g.1.1 •
    TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2))
      (SixQuarkTypedFlavor.slotRepresentation U D up down i g.1.2) (v i)) = f v
  rw [f.map_smul_univ, phase_product, one_smul]
  simp_rw [split_action, LinearMap.comp_apply]
  rw [hf.1, hf.2, hr]

private theorem colorAction_one : colorAction (1 : SixColorInvariant.Group) = LinearMap.id := by
  simp [colorAction, Module.End.one_eq_id]

private theorem spinAction_one : spinAction (1 : WeylSpinor.Group) = LinearMap.id := by
  simp [spinAction, Module.End.one_eq_id]

/-- Necessity as well as sufficiency: independent invariances are recovered by
testing the physical group on its color, Weyl and residual factors. -/
theorem physical_invariance_iff
    (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D)) :
    IsPhysicalInvariant up down f ↔
      IsInvariant f ∧ IsResidualInvariant (SixQuarkTypedFlavor.slotRepresentation U D up down) f := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro c v
      have he := h (((c, 1, 1), 1), 1) v
      simpa [slotAction, StandardSMGaugeTensor.phase, spinAction_one, Module.End.one_eq_id] using he
    · intro s v
      have he := h ((1, 1), s) v
      simpa [slotAction, colorAction_one, Module.End.one_eq_id] using he
    · intro a v
      have he := h ((1, a), 1) v
      simpa [slotAction, colorAction_one, spinAction_one, Module.End.one_eq_id] using he
  · rintro ⟨hf, hr⟩
    exact physical_invariant up down f hf hr

abbrev UpField := (SMEpsilonTensor.Color ⊗[ℂ] U) ⊗[ℂ] Spin
abbrev DownField := (SMEpsilonTensor.Color ⊗[ℂ] D) ⊗[ℂ] Spin
abbrev TotalField := UpField (U := U) × DownField (D := D)

def embedFlavor (b : Bool) :
    Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b →ₗ[ℂ] TotalField (U := U) (D := D) :=
  match b with
  | true => (LinearMap.inl ℂ _ _).comp reorder.symm.toLinearMap
  | false => (LinearMap.inr ℂ _ _).comp reorder.symm.toLinearMap

abbrev embedSlot (i : Fin 6) := embedFlavor (U := U) (D := D) (decide (i = 0 ∨ i = 2))

theorem embedSlot_action (g : SymmetryGroup H) (i : Fin 6)
    (v : Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i) :
    SixSlotAlternation.action (upModel up) (downModel down) g (embedSlot i v) =
      embedSlot i (slotAction up down g i v) := by
  have he (b : Bool) (v : Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b) :
      SixSlotAlternation.action (upModel up) (downModel down) g (embedFlavor b v) =
        embedFlavor b (StandardSMGaugeTensor.phase (if b then 4 else -2) g.1.1 •
          TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2))
            (SixQuarkTypedFlavor.flavorRepresentation U D up down b g.1.2) v) := by
    cases b
    · apply Prod.ext
      · simp [embedFlavor, LinearMap.comp_apply]
      · change downModel down g (reorder.symm v) = reorder.symm _
        apply reorder.injective
        simp [reorder_down_action, SixQuarkTypedFlavor.flavorRepresentation]
    · apply Prod.ext
      · change upModel up g (reorder.symm v) = reorder.symm _
        apply reorder.injective
        simp [reorder_up_action, SixQuarkTypedFlavor.flavorRepresentation]
      · simp [embedFlavor, LinearMap.comp_apply]
  simpa [embedSlot, slotAction, charge, SixQuarkTypedFlavor.slotRepresentation] using
    he (decide (i = 0 ∨ i = 2)) v

attribute [local irreducible] upModel downModel reorder embedFlavor SixSlotSpeciesDegree.sector

def restrictEvaluation (ev : TotalField (U := U) (D := D) [⋀^Fin 6]→ₗ[ℂ] ℂ) :
    FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D) :=
  ev.toMultilinearMap.compLinearMap (fun i => embedSlot (U := U) (D := D) i)

def physicalEvaluation (f : ModelSector up down) :
    TotalField (U := U) (D := D) [⋀^Fin 6]→ₗ[ℂ] ℂ :=
  SixSlotSpeciesRestriction.evaluation
    (H := SymmetryGroup H) (A := UpField (U := U)) (B := DownField (D := D))
      (upModel up) (downModel down) f.val

@[simp] theorem physicalEvaluation_apply (f : ModelSector up down)
    (v : Fin 6 → TotalField (U := U) (D := D)) :
    physicalEvaluation up down f v = f.val (exteriorPower.ιMulti ℂ 6 v) := rfl

/-- Restriction of an actual independent exterior coefficient to reordered,
heterogeneous flavor slots. This is not a contraction ansatz. -/
def restrictSector (f : ModelSector up down) :
    FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D) :=
  restrictEvaluation (physicalEvaluation up down f)

theorem restrictSector_physicalInvariant (f : ModelSector up down) :
    IsPhysicalInvariant up down (restrictSector up down f) := by
  intro g v
  change f.val (exteriorPower.ιMulti ℂ 6 (fun i => embedSlot i (slotAction up down g i (v i)))) =
    f.val (exteriorPower.ιMulti ℂ 6 (fun i => embedSlot i (v i)))
  simp_rw [← embedSlot_action]
  have he := Representation.IntertwiningMap.isIntertwining _ _ f.val g
    (exteriorPower.ιMulti ℂ 6 (fun i => embedSlot i (v i)))
  simpa only [Representation.exteriorPower_apply_ιMulti, Function.comp_def,
    Representation.trivial_apply, LinearMap.id_apply] using he

theorem restrictSector_invariant (f : ModelSector up down) :
    IsInvariant (restrictSector up down f) ∧
      IsResidualInvariant (SixQuarkTypedFlavor.slotRepresentation U D up down)
        (restrictSector up down f) :=
  (physical_invariance_iff up down _).mp (restrictSector_physicalInvariant up down f)

theorem embedSlot_exchange (g : Fin 4) (i : Fin 6)
    (q : Fin 6 → Quark) (t : ∀ j, SixQuarkTypedFlavor.SlotFlavor U D j) :
    embedSlot i (q (SixQuarkSpeciesQuotient.slotSwap g i) ⊗ₜ[ℂ]
      exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t i) =
        embedSlot (SixQuarkSpeciesQuotient.slotSwap g i)
          (q (SixQuarkSpeciesQuotient.slotSwap g i) ⊗ₜ[ℂ]
            t (SixQuarkSpeciesQuotient.slotSwap g i)) := by
  fin_cases g <;> fin_cases i <;>
    simp [embedSlot, exchangeFlavor, SixQuarkTypedFlavor.speciesExchange,
      SixQuarkSpeciesQuotient.slotSwap, Equiv.swap_apply_def]
  all_goals rfl

theorem restrictEvaluation_typedAlternating
    (ev : TotalField (U := U) (D := D) [⋀^Fin 6]→ₗ[ℂ] ℂ) :
    IsTypedSwapAlternating (SixQuarkTypedFlavor.speciesExchange U D)
      (restrictEvaluation ev) := by
  intro g q t
  have he := ev.map_congr_perm (fun i => embedSlot i (q i ⊗ₜ[ℂ] t i))
    (SixQuarkSpeciesQuotient.slotSwap g)
  have hv : (fun i => embedSlot i (q i ⊗ₜ[ℂ] t i)) ∘ SixQuarkSpeciesQuotient.slotSwap g =
      (fun i => embedSlot i (q (SixQuarkSpeciesQuotient.slotSwap g i) ⊗ₜ[ℂ]
        exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t i)) := by
    funext i
    exact (embedSlot_exchange g i q t).symm
  rw [hv] at he
  have hs : Equiv.Perm.sign (SixQuarkSpeciesQuotient.slotSwap g) = -1 := by
    fin_cases g <;> decide
  rw [hs] at he
  change ev (fun i => embedSlot i
    (q (SixQuarkSpeciesQuotient.slotSwap g i) ⊗ₜ[ℂ]
      exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t i)) =
    -ev (fun i => embedSlot i (q i ⊗ₜ[ℂ] t i))
  simpa using (congrArg Neg.neg he).symm

theorem restrictSector_typedAlternating (f : ModelSector up down) :
    IsTypedSwapAlternating (SixQuarkTypedFlavor.speciesExchange U D)
      (restrictSector up down f) :=
  restrictEvaluation_typedAlternating _

def restrictedCoefficient (f : ModelSector up down) : SixQuarkTypedFlavor.Coefficients U D up down :=
  ⟨restrictSector up down f, (restrictSector_invariant up down f).1,
    (restrictSector_invariant up down f).2, restrictSector_typedAlternating up down f⟩

def projectFlavor (b : Bool) : TotalField (U := U) (D := D) →ₗ[ℂ]
    Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b :=
  match b with
  | true => reorder.toLinearMap.comp (LinearMap.fst ℂ _ _)
  | false => reorder.toLinearMap.comp (LinearMap.snd ℂ _ _)

abbrev projectSlot (i : Fin 6) := projectFlavor (U := U) (D := D) (decide (i = 0 ∨ i = 2))

attribute [local semireducible] embedFlavor

theorem embed_project_slots (a c : UpField (U := U)) (b d e x : DownField (D := D)) :
    (fun i => embedSlot i (projectSlot i (SixSlotAlternation.slots a c b d e x i))) =
      SixSlotAlternation.slots a c b d e x := by
  funext i
  fin_cases i
  · change (reorder.symm (reorder a), 0) = (a, 0); rw [LinearEquiv.symm_apply_apply]
  · change (0, reorder.symm (reorder b)) = (0, b); rw [LinearEquiv.symm_apply_apply]
  · change (reorder.symm (reorder c), 0) = (c, 0); rw [LinearEquiv.symm_apply_apply]
  · change (0, reorder.symm (reorder d)) = (0, d); rw [LinearEquiv.symm_apply_apply]
  · change (0, reorder.symm (reorder e)) = (0, e); rw [LinearEquiv.symm_apply_apply]
  · change (0, reorder.symm (reorder x)) = (0, x); rw [LinearEquiv.symm_apply_apply]

attribute [local irreducible] restrictSector restrictEvaluation

theorem restriction_slots_eq
    (ev ew : TotalField (U := U) (D := D) [⋀^Fin 6]→ₗ[ℂ] ℂ)
    (h : restrictEvaluation ev = restrictEvaluation ew)
    (a c : UpField (U := U)) (b d e x : DownField (D := D)) :
    ev (SixSlotAlternation.slots a c b d e x) =
      ew (SixSlotAlternation.slots a c b d e x) := by
  have he := DFunLike.congr_fun h
    (fun i => projectSlot i (SixSlotAlternation.slots a c b d e x i))
  unfold restrictEvaluation at he
  change ev (fun i => embedSlot i (projectSlot i (SixSlotAlternation.slots a c b d e x i))) =
    ew (fun i => embedSlot i (projectSlot i (SixSlotAlternation.slots a c b d e x i))) at he
  simpa only [embed_project_slots] using he

attribute [local irreducible] SixSlotSpeciesRestriction.evaluation physicalEvaluation

/-- Extend a typed coefficient by projecting each input to its prescribed species. -/
def projected (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D)) :
    MultilinearMap ℂ (fun _ : Fin 6 => TotalField (U := U) (D := D)) ℂ :=
  f.compLinearMap (fun i => projectSlot i)

theorem projectSlot_exchange (g : Fin 4) (i : Fin 6)
    (v : TotalField (U := U) (D := D)) :
    SixQuarkTypedFlavor.tensorExchange U D g i
      (projectSlot (SixQuarkSpeciesQuotient.slotSwap g i) v) = projectSlot i v := by
  fin_cases g <;> fin_cases i
  all_goals first
    | change TensorProduct.congr (LinearEquiv.refl ℂ Quark) (LinearEquiv.refl ℂ U)
        (reorder v.1) = reorder v.1
    | change TensorProduct.congr (LinearEquiv.refl ℂ Quark) (LinearEquiv.refl ℂ D)
        (reorder v.2) = reorder v.2
  all_goals simp only [TensorProduct.congr_refl_refl, LinearEquiv.refl_apply]

theorem projected_species (f : SixQuarkTypedFlavor.Coefficients U D up down)
    (p : Equiv.Perm (Fin 6)) (hp : SixSlotAlternation.PreservesPattern p)
    (v : Fin 6 → TotalField (U := U) (D := D)) :
    projected f.val (v ∘ p) = Equiv.Perm.sign p • projected f.val v := by
  apply SixQuarkSpeciesQuotient.generators_species_sign _ _ p hp v
  intro g w
  have he := SixQuarkTypedFlavor.typed_swap_full U D f.val f.property.2.2 g
    (fun i => projectSlot i (w i))
  simpa only [projected, MultilinearMap.compLinearMap_apply,
    projectSlot_exchange, Function.comp_def] using he

theorem projectSlot_action (g : SymmetryGroup H) (i : Fin 6)
    (v : TotalField (U := U) (D := D)) :
    projectSlot i (SixSlotAlternation.action (upModel up) (downModel down) g v) =
      slotAction up down g i (projectSlot i v) := by
  have he (b : Bool) :
      projectFlavor b (SixSlotAlternation.action (upModel up) (downModel down) g v) =
        StandardSMGaugeTensor.phase (if b then 4 else -2) g.1.1 •
          TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2))
            (SixQuarkTypedFlavor.flavorRepresentation U D up down b g.1.2)
            (projectFlavor b v) := by
    cases b
    · exact reorder_down_action down g v.2
    · exact reorder_up_action up g v.1
  simpa [projectSlot, slotAction, charge, SixQuarkTypedFlavor.slotRepresentation] using
    he (decide (i = 0 ∨ i = 2))

theorem projected_invariant (f : SixQuarkTypedFlavor.Coefficients U D up down)
    (g : SymmetryGroup H) (v : Fin 6 → TotalField (U := U) (D := D)) :
    projected f.val (fun i => SixSlotAlternation.action (upModel up) (downModel down) g (v i)) =
      projected f.val v := by
  change f.val (fun i => projectSlot i
    (SixSlotAlternation.action (upModel up) (downModel down) g (v i))) = _
  simp_rw [projectSlot_action]
  exact physical_invariant up down f.val f.property.1 f.property.2.1 g _

def normalizedAlternating (f : SixQuarkTypedFlavor.Coefficients U D up down) :
    TotalField (U := U) (D := D) [⋀^Fin 6]→ₗ[ℂ] ℂ :=
  (1 / 48 : ℂ) • (projected f.val).alternatization

theorem normalizedAlternating_invariant
    (f : SixQuarkTypedFlavor.Coefficients U D up down) (g : SymmetryGroup H)
    (v : Fin 6 → TotalField (U := U) (D := D)) :
    normalizedAlternating up down f
      (fun i => SixSlotAlternation.action (upModel up) (downModel down) g (v i)) =
      normalizedAlternating up down f v := by
  simp only [normalizedAlternating, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [projected_invariant up down f g (fun i => v (p i))]

attribute [local irreducible] Representation.prod Representation.exteriorPower
  Representation.trivial
attribute [local irreducible] projected normalizedAlternating SixSlotSpeciesRestriction.ofEvaluation

def descended (f : SixQuarkTypedFlavor.Coefficients U D up down) :
    SixSlotSpeciesDegree.coefficients (H := SymmetryGroup H)
      (A := UpField (U := U)) (B := DownField (D := D)) (upModel up) (downModel down) :=
  SixSlotSpeciesRestriction.ofEvaluation (H := SymmetryGroup H)
    (A := UpField (U := U)) (B := DownField (D := D)) (upModel up) (downModel down)
    (normalizedAlternating up down f) (normalizedAlternating_invariant up down f)

@[simp] theorem descended_apply (f : SixQuarkTypedFlavor.Coefficients U D up down)
    (v : Fin 6 → TotalField (U := U) (D := D)) :
    descended up down f (exteriorPower.ιMulti ℂ 6 v) =
      normalizedAlternating up down f v :=
  SixSlotSpeciesRestriction.ofEvaluation_apply _ _ _ _ _

def speciesScale (r s : ℂ) (i : Fin 6) : ℂ := if i = 0 ∨ i = 2 then r else s

theorem projectSlot_scaling (r s : ℂ) (i : Fin 6)
    (v : TotalField (U := U) (D := D)) :
    projectSlot i (SixSlotSpeciesDegree.scaling (upModel up) (downModel down) r s v) =
      speciesScale r s i • projectSlot i v := by
  have he (b : Bool) :
      projectFlavor b (SixSlotSpeciesDegree.scaling (upModel up) (downModel down) r s v) =
        (if b then r else s) • projectFlavor b v := by
    cases b <;> simp [projectFlavor, SixSlotSpeciesDegree.scaling]
  simpa [projectSlot, speciesScale] using he (decide (i = 0 ∨ i = 2))

theorem speciesScale_product (r s : ℂ) :
    (∏ i : Fin 6, speciesScale r s i) = r * r * s * s * s * s := by
  simp [speciesScale, Fin.prod_univ_succ]
  ring

theorem projected_scaling (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D))
    (r s : ℂ) (v : Fin 6 → TotalField (U := U) (D := D)) :
    projected f (fun i => SixSlotSpeciesDegree.scaling (upModel up) (downModel down) r s (v i)) =
      (r * r * s * s * s * s) • projected f v := by
  unfold projected
  change f (fun i => projectSlot i
    (SixSlotSpeciesDegree.scaling (upModel up) (downModel down) r s (v i))) = _
  simp_rw [projectSlot_scaling]
  rw [f.map_smul_univ, speciesScale_product]
  rfl

theorem normalizedAlternating_scaling
    (f : SixQuarkTypedFlavor.Coefficients U D up down) (r s : ℂ)
    (v : Fin 6 → TotalField (U := U) (D := D)) :
    normalizedAlternating up down f
      (fun i => SixSlotSpeciesDegree.scaling (upModel up) (downModel down) r s (v i)) =
      (r * r * s * s * s * s) • normalizedAlternating up down f v := by
  simp only [normalizedAlternating, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]
  rw [smul_comm (r * r * s * s * s * s) (1 / 48 : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [projected_scaling up down _ r s (fun i => v (p i)), smul_comm]

theorem descended_degree (f : SixQuarkTypedFlavor.Coefficients U D up down) :
    SixSlotSpeciesDegree.HasDegree (H := SymmetryGroup H)
      (A := UpField (U := U)) (B := DownField (D := D))
      (upModel up) (downModel down) (descended up down f) := by
  exact SixSlotSpeciesRestriction.ofEvaluation_degree
    (H := SymmetryGroup H) (A := UpField (U := U)) (B := DownField (D := D))
    (upModel up) (downModel down) (normalizedAlternating up down f)
    (normalizedAlternating_invariant up down f) (normalizedAlternating_scaling up down f)

def liftSector (f : SixQuarkTypedFlavor.Coefficients U D up down) : ModelSector up down :=
  ⟨descended up down f, by
    unfold SixSlotSpeciesDegree.sector
    change SixSlotSpeciesDegree.HasDegree (H := SymmetryGroup H)
      (A := UpField (U := U)) (B := DownField (D := D)) (upModel up) (downModel down) _
    exact descended_degree up down f⟩

theorem projected_bad (f : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D))
    (a c : UpField (U := U)) (b d e x : DownField (D := D))
    (p : Equiv.Perm (Fin 6)) (hp : ¬ SixSlotAlternation.PreservesPattern p) :
    projected f (SixSlotAlternation.slots a c b d e x ∘ p) = 0 := by
  unfold projected
  change f (fun i => projectSlot i (SixSlotAlternation.slots a c b d e x (p i))) = 0
  by_cases h0 : p 0 = 0 ∨ p 0 = 2
  · have h2 : ¬ (p 2 = 0 ∨ p 2 = 2) := fun h => hp ⟨h0, h⟩
    apply f.map_coord_zero 2
    change reorder (SixSlotAlternation.slots a c b d e x (p 2)).1 = 0
    generalize hk : p 2 = k
    fin_cases k <;> simp_all [SixSlotAlternation.slots]

  · apply f.map_coord_zero 0
    change reorder (SixSlotAlternation.slots a c b d e x (p 0)).1 = 0
    generalize hk : p 0 = k
    fin_cases k <;> simp_all [SixSlotAlternation.slots]

theorem normalizedAlternating_slots (f : SixQuarkTypedFlavor.Coefficients U D up down)
    (a c : UpField (U := U)) (b d e x : DownField (D := D)) :
    normalizedAlternating up down f (SixSlotAlternation.slots a c b d e x) =
      projected f.val (SixSlotAlternation.slots a c b d e x) := by
  have hn := SixSlotSpeciesRestriction.alternatization_slots
      (A := UpField (U := U)) (B := DownField (D := D))
      (projected f.val) (SixSlotAlternation.slots a c b d e x)
      (fun p hp => projected_species up down f p hp _)
      (fun p hp => projected_bad f.val a c b d e x p hp)
  rw [normalizedAlternating, AlternatingMap.smul_apply, hn]
  simp only [smul_eq_mul]
  ring

theorem projectSlot_embedSlot (i : Fin 6)
    (v : Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i) :
    projectSlot i (embedSlot i v) = v := by
  have he (b : Bool) (w : Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b) :
      projectFlavor b (embedFlavor b w) = w := by
    cases b <;> simp [projectFlavor, embedFlavor]
  exact he (decide (i = 0 ∨ i = 2)) v

theorem restrict_lift (f : SixQuarkTypedFlavor.Coefficients U D up down) :
    restrictSector up down (liftSector up down f) = f.val := by
  ext v
  unfold restrictSector restrictEvaluation
  change physicalEvaluation up down (liftSector up down f) (fun i => embedSlot i (v i)) = f.val v
  rw [physicalEvaluation_apply]
  change descended up down f (exteriorPower.ιMulti ℂ 6 (fun i => embedSlot i (v i))) = _
  rw [descended_apply]
  have hs : (fun i => embedSlot i (v i)) = SixSlotAlternation.slots
      (reorder.symm (v 0)) (reorder.symm (v 2)) (reorder.symm (v 1))
      (reorder.symm (v 3)) (reorder.symm (v 4)) (reorder.symm (v 5)) := by
    funext i
    fin_cases i <;> rfl
  rw [hs, normalizedAlternating_slots, ← hs]
  unfold projected
  change f.val (fun i => projectSlot i (embedSlot i (v i))) = f.val v
  simp only [projectSlot_embedSlot]

theorem restrictSector_injective : Function.Injective (restrictSector up down) := by
  intro f k h
  unfold restrictSector at h
  have hs := restriction_slots_eq _ _ h
  unfold physicalEvaluation at hs
  exact SixSlotSpeciesRestriction.sector_ext
    (H := SymmetryGroup H) (A := UpField (U := U)) (B := DownField (D := D))
    (upModel up) (downModel down) f k hs


/-- Actual exterior coefficients yield constrained residual Hom coordinates.
The inverse is the normalized alternating lift in `sectorHomEquiv`. -/
def sectorHom (f : ModelSector up down) : SixQuarkTypedFlavor.StatisticsHom U D up down :=
  SixQuarkTypedFlavor.homLinearEquiv U D up down (restrictedCoefficient up down f)

/-- The physical extraction is linear. -/
def restrictedCoefficientLinear : ModelSector up down →ₗ[ℂ]
    SixQuarkTypedFlavor.Coefficients U D up down where
  toFun := restrictedCoefficient up down
  map_add' f k := by
    apply Subtype.ext
    ext v
    unfold restrictedCoefficient restrictSector restrictEvaluation physicalEvaluation
      SixSlotSpeciesRestriction.evaluation
    rfl
  map_smul' z f := by
    apply Subtype.ext
    ext v
    unfold restrictedCoefficient restrictSector restrictEvaluation physicalEvaluation
      SixSlotSpeciesRestriction.evaluation
    rfl

theorem lift_restrictedCoefficient (f : ModelSector up down) :
    liftSector up down (restrictedCoefficient up down f) = f := by
  apply restrictSector_injective up down
  rw [restrict_lift]
  rfl

/-- Full physical classification, with the normalized exterior lift as inverse. -/
def sectorCoefficientEquiv : ModelSector up down ≃ₗ[ℂ]
    SixQuarkTypedFlavor.Coefficients U D up down where
  toFun := restrictedCoefficient up down
  invFun := liftSector up down
  left_inv := lift_restrictedCoefficient up down
  right_inv f := Subtype.ext (restrict_lift up down f)
  map_add' := (restrictedCoefficientLinear up down).map_add
  map_smul' := (restrictedCoefficientLinear up down).map_smul

def sectorHomEquiv : ModelSector up down ≃ₗ[ℂ]
    SixQuarkTypedFlavor.StatisticsHom U D up down :=
  (sectorCoefficientEquiv up down).trans (SixQuarkTypedFlavor.homLinearEquiv U D up down)

@[simp] theorem sectorHomEquiv_apply (f : ModelSector up down) :
    sectorHomEquiv up down f = sectorHom up down f := rfl

@[simp] theorem sectorHomEquiv_symm_apply
    (k : SixQuarkTypedFlavor.StatisticsHom U D up down) :
    (sectorHomEquiv up down).symm k =
      liftSector up down ((SixQuarkTypedFlavor.homLinearEquiv U D up down).symm k) := rfl

theorem sectorHom_surjective : Function.Surjective (sectorHom up down) :=
  (sectorHomEquiv up down).surjective

theorem exists_nonzero_sector_iff :
    (∃ f : ModelSector up down, f ≠ 0) ↔
      ∃ k : SixQuarkTypedFlavor.StatisticsHom U D up down, k ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨sectorHomEquiv up down f,
      fun h => hf ((sectorHomEquiv up down).map_eq_zero_iff.mp h)⟩
  · rintro ⟨k, hk⟩
    exact ⟨(sectorHomEquiv up down).symm k,
      fun h => hk ((sectorHomEquiv up down).symm.map_eq_zero_iff.mp h)⟩

def sectorHomLinear : ModelSector up down →ₗ[ℂ]
    SixQuarkTypedFlavor.StatisticsHom U D up down :=
  (SixQuarkTypedFlavor.homLinearEquiv U D up down).toLinearMap.comp
    (restrictedCoefficientLinear up down)

theorem sectorHom_injective : Function.Injective (sectorHom up down) := by
  intro f k h
  have hc := (SixQuarkTypedFlavor.homLinearEquiv U D up down).injective h
  exact restrictSector_injective up down (congrArg Subtype.val hc)

/-- A physical coefficient is nonzero exactly when its extracted Hom is nonzero.
This does not assert that every constrained Hom has a physical preimage. -/
theorem sectorHom_ne_zero_iff (f : ModelSector up down) :
    sectorHom up down f ≠ 0 ↔ f ≠ 0 := by
  have hz : sectorHom up down 0 = 0 := (sectorHomLinear up down).map_zero
  constructor
  · intro h hf
    exact h (hf ▸ hz)
  · intro h hf
    exact h (sectorHom_injective up down (hf.trans hz.symm))

section ActualFields

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ (SymmetryGroup H) A)
  (b : Representation ℂ (SymmetryGroup H) B)
  (input : Inputs up down a b)

/-- Extraction on actual fields uses the supplied representation correspondence. -/
def onFieldsHomEquiv : SixSlotSpeciesDegree.sector a b ≃ₗ[ℂ]
    SixQuarkTypedFlavor.StatisticsHom U D up down :=
  (onFieldsEquiv up down a b input).symm.trans (sectorHomEquiv up down)

@[simp] theorem onFieldsHomEquiv_symm_apply
    (k : SixQuarkTypedFlavor.StatisticsHom U D up down) :
    (onFieldsHomEquiv up down a b input).symm k =
      onFieldsEquiv up down a b input ((sectorHomEquiv up down).symm k) := rfl

include input in
theorem exists_nonzero_onFields_iff :
    (∃ f : SixSlotSpeciesDegree.sector a b, f ≠ 0) ↔
      ∃ k : SixQuarkTypedFlavor.StatisticsHom U D up down, k ≠ 0 :=
  (DeltaBTwoModelInterface.exists_on_fields_iff up down a b input).trans
    (exists_nonzero_sector_iff up down)

def onFieldsHomLinear : SixSlotSpeciesDegree.sector a b →ₗ[ℂ]
    SixQuarkTypedFlavor.StatisticsHom U D up down :=
  (sectorHomLinear up down).comp (onFieldsEquiv up down a b input).symm.toLinearMap

theorem onFieldsHom_injective : Function.Injective (onFieldsHomLinear up down a b input) :=
  (sectorHom_injective up down).comp (onFieldsEquiv up down a b input).symm.injective

theorem onFieldsHom_ne_zero_iff (f : SixSlotSpeciesDegree.sector a b) :
    onFieldsHomLinear up down a b input f ≠ 0 ↔ f ≠ 0 := by
  have hz := (onFieldsHomLinear up down a b input).map_zero
  constructor
  · intro h hf
    exact h (hf ▸ hz)
  · intro h hf
    exact h (onFieldsHom_injective up down a b input (hf.trans hz.symm))

end ActualFields

end
end Physics.DeltaBTwoFlavorBridge
