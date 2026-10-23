import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorOneGeneration
import Math.RepresentationTheory.Constructions.TypedMixedSeparatedHom
import Math.LinearAlgebra.Constructions.LinearEquivComparison
import Mathlib.Tactic.IrreducibleDef

open Math

/-! Specified physical u²d⁴ coefficients and the degree-uniform quotient. -/
namespace Physics.GradedSixQuarkComparison
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Representation ExternalInvariantTensor SixQuarkInvariant SixQuarkFlavorCoordinates
open scoped TensorProduct
universe u
variable {R : Type*} [Group R] (U D : Type u)
  [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  (up : Representation ℂ R U) (down : Representation ℂ R D)

def localQuark (_b : Bool) := external
  (if _b then StandardSMGaugeTensor.upRight else StandardSMGaugeTensor.downRight)
  WeylSpinor.right
def scalarLocal (_ : Unit) := trivial ℂ
  (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) ℂ
abbrev flavor := SixQuarkTypedFlavor.flavorRepresentation U D up down
def scalarFlavor (_ : Unit) := trivial ℂ R ℂ
abbrev pattern (i : Fin 6) : Bool := decide (i = 0 ∨ i = 2)
def scalars (i : Fin 0) : Unit := Fin.elim0 i
abbrev fermion := TypedMixedSeparatedHom.fieldF localQuark (flavor U D up down)
abbrev boson := TypedMixedSeparatedHom.fieldB scalarLocal (scalarFlavor (R := R))
abbrev Ordered := MixedPatternAssembly.orderedSpace
  (fermion U D up down) (boson (R := R)) pattern scalars
abbrev Residual := IntertwiningMap
  (TypedMixedSeparatedHom.residual localQuark scalarLocal (flavor U D up down)
    (scalarFlavor (R := R)) pattern scalars) (trivial ℂ R ℂ)

theorem field_apply (g : DeltaBTwoModelInterface.SymmetryGroup R) (i : Fin 6)
    (v : Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i) :
    fermion U D up down (pattern i) ((g.1.1,g.2),g.1.2) v =
      DeltaBTwoFlavorBridge.slotAction up down g i v := by
  rcases g with ⟨⟨cG,r⟩,sG⟩
  induction v using TensorProduct.inductionOn with
  | tmul q t =>
    induction q using TensorProduct.inductionOn with
    | tmul c s =>
      by_cases hi : i = 0 ∨ i = 2 <;>
        simp [fermion, TypedMixedSeparatedHom.fieldF, TypedMixedLocalHom.fermion,
          TypedMixedSeparatedHom.localF, TypedMixedSeparatedHom.residualF,
          CommutingActionHom.action_apply, localQuark, flavor, pattern, hi,
          SixQuarkTypedFlavor.slotRepresentation, DeltaBTwoFlavorBridge.slotAction,
          DeltaBTwoFlavorBridge.charge, external, Representation.tprod_apply,
          StandardSMGaugeTensor.upRight, StandardSMGaugeTensor.downRight,
          StandardSMGaugeTensor.twist, colorAction, spinAction,
          StandardSMGaugeTensor.color, TensorProduct.smul_tmul'] <;> rfl
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

def emptyEquiv : FlavorCoefficient (V := SixQuarkTypedFlavor.SlotFlavor U D) ≃ₗ[ℂ]
    MixedPatternAssembly.Ordered
      (V := fun b => Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b)
      (W := fun _ : Unit => ℂ ⊗[ℂ] ℂ) pattern scalars :=
  (MultilinearMap.constLinearEquivOfIsEmpty ℂ ℂ
    (fun _ : Fin 0 => ℂ ⊗[ℂ] ℂ) ℂ).multilinearMapCongrRight ℂ

theorem emptyEquiv_symm_apply (k : MixedPatternAssembly.Ordered
    (V := fun b => Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b)
    (W := fun _ : Unit => ℂ ⊗[ℂ] ℂ) pattern scalars)
    (v : ∀ i, Quark ⊗[ℂ] SixQuarkTypedFlavor.SlotFlavor U D i)
    (w : Fin 0 → ℂ ⊗[ℂ] ℂ) : (emptyEquiv U D).symm k v = k v w := by
  change k v 0 = k v w
  exact congrArg (k v) (Subsingleton.elim _ _)

def toOrdered (f : SixQuarkTypedFlavor.Coefficients U D up down) : Ordered U D up down := by
  refine ⟨emptyEquiv U D f.val, ?_, ?_, ?_⟩
  · rintro ⟨⟨g,s⟩,r⟩ v w
    change f.val (fun i => fermion U D up down (pattern i) ((g,s),r) (v i)) = f.val v
    simp only [field_apply U D up down ((g,r),s)]
    exact DeltaBTwoFlavorBridge.physical_invariant up down f.val f.property.1 f.property.2.1
      ((g,r),s) v
  · intro p hp w
    apply MultilinearMap.ext
    intro z
    have he := (DeltaBTwoFlavorBridge.physicalEvaluation up down
      (DeltaBTwoFlavorBridge.liftSector up down f)).map_congr_perm
      (fun i => DeltaBTwoFlavorBridge.embedFlavor (pattern i) (w i (pattern i))) p
    have hv : (fun i => DeltaBTwoFlavorBridge.embedFlavor (pattern i) (w i (pattern i))) ∘ p =
        fun i => DeltaBTwoFlavorBridge.embedFlavor (pattern i) (w (p i) (pattern i)) := by
      funext i
      have hi := congrFun hp i
      dsimp only [Function.comp_apply] at hi ⊢
      rw [hi]
    rw [hv] at he
    have hf := DeltaBTwoFlavorBridge.restrict_lift up down f
    change Equiv.Perm.sign p • f.val (fun i => w (p i) (pattern i)) =
      f.val (fun i => w i (pattern i))
    rw [← hf]
    exact he.symm
  · intro v p hp w; rfl

def fromOrdered (k : Ordered U D up down) : SixQuarkTypedFlavor.Coefficients U D up down := by
  let f := (emptyEquiv U D).symm k.val
  have hinv : DeltaBTwoFlavorBridge.IsPhysicalInvariant up down f := by
    intro g v
    have he := k.property.1 ((g.1.1,g.2),g.1.2) v (fun i => Fin.elim0 i)
    have hw : (fun j => boson (R := R) (scalars j) ((g.1.1,g.2),g.1.2)
        (Fin.elim0 j)) = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    rw [hw] at he
    have hv : (fun i => fermion U D up down (pattern i) ((g.1.1,g.2),g.1.2) (v i)) =
        (fun i => DeltaBTwoFlavorBridge.slotAction up down g i (v i)) := by
      funext i; exact field_apply U D up down g i (v i)
    rw [hv] at he
    simpa only [f, emptyEquiv_symm_apply U D (w := fun i => Fin.elim0 i)] using he
  refine ⟨f, ((DeltaBTwoFlavorBridge.physical_invariance_iff up down f).mp hinv).1,
    ((DeltaBTwoFlavorBridge.physical_invariance_iff up down f).mp hinv).2, ?_⟩
  intro g q t
  let w : Fin 6 → ∀ b, Quark ⊗[ℂ] SixQuarkTypedFlavor.Flavor U D b :=
    fun i => Pi.single (pattern i) (q i ⊗ₜ[ℂ] t i)
  have hp : pattern ∘ SixQuarkSpeciesQuotient.slotSwap g = pattern := by
    fin_cases g <;> decide
  have he := congrArg (fun z => z (fun i => Fin.elim0 i))
    (k.property.2.1 (SixQuarkSpeciesQuotient.slotSwap g) hp w)
  have he' : Equiv.Perm.sign (SixQuarkSpeciesQuotient.slotSwap g) •
      f (fun i => w (SixQuarkSpeciesQuotient.slotSwap g i) (pattern i)) =
      f (fun i => w i (pattern i)) := by
    change Equiv.Perm.sign (SixQuarkSpeciesQuotient.slotSwap g) •
      k.val (fun i => w (SixQuarkSpeciesQuotient.slotSwap g i) (pattern i))
        (fun i => Fin.elim0 i) = k.val (fun i => w i (pattern i)) (fun i => Fin.elim0 i) at he
    simpa only [f, emptyEquiv_symm_apply U D (w := fun i => Fin.elim0 i)] using he
  have hs : Equiv.Perm.sign (SixQuarkSpeciesQuotient.slotSwap g) = -1 := by
    fin_cases g <;> decide
  have hv : (fun i => w (SixQuarkSpeciesQuotient.slotSwap g i) (pattern i)) =
      (fun i => q (SixQuarkSpeciesQuotient.slotSwap g i) ⊗ₜ[ℂ]
        exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t i) := by
    funext i
    fin_cases g <;> fin_cases i <;>
      simp [w, pattern, SixQuarkSpeciesQuotient.slotSwap, exchangeFlavor,
        SixQuarkTypedFlavor.speciesExchange, Equiv.swap_apply_def]
    all_goals rfl
  have hw : (fun i => w i (pattern i)) = fun i => q i ⊗ₜ[ℂ] t i := by
    funext i; simp [w]
  rw [hs, hv, hw] at he'
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul] at he'
  exact neg_eq_iff_eq_neg.mp he'

def orderedEquiv : SixQuarkTypedFlavor.Coefficients U D up down ≃ₗ[ℂ] Ordered U D up down where
  toFun := toOrdered U D up down
  invFun := fromOrdered U D up down
  left_inv f := by
    apply Subtype.ext
    change (emptyEquiv U D).symm ((emptyEquiv U D) f.val) = f.val
    exact (emptyEquiv U D).symm_apply_apply f.val
  right_inv k := by
    apply Subtype.ext
    change (emptyEquiv U D) ((emptyEquiv U D).symm k.val) = k.val
    exact (emptyEquiv U D).apply_symm_apply k.val
  map_add' f k := by apply Subtype.ext; exact (emptyEquiv U D).map_add f.val k.val
  map_smul' z f := by apply Subtype.ext; exact (emptyEquiv U D).map_smul z f.val

irreducible_def equiv : DeltaBTwoModelInterface.ModelSector up down ≃ₗ[ℂ] Residual U D up down :=
  (DeltaBTwoFlavorBridge.sectorCoefficientEquiv up down).trans
    ((orderedEquiv U D up down).trans (TypedMixedSeparatedHom.equiv localQuark scalarLocal
      (flavor U D up down) (scalarFlavor (R := R)) pattern scalars))

def comparison : Residual U D up down ≃ₗ[ℂ] SixQuarkTypedFlavor.StatisticsHom U D up down :=
  LinearEquivComparison.comparison (equiv U D up down) (DeltaBTwoFlavorBridge.sectorHomEquiv up down)

attribute [local irreducible] comparison

theorem extraction_commutes (f : DeltaBTwoModelInterface.ModelSector up down) :
    comparison U D up down (equiv U D up down f) =
      DeltaBTwoFlavorBridge.sectorHomEquiv up down f := by
  unfold comparison
  exact LinearEquivComparison.extraction (equiv U D up down)
    (DeltaBTwoFlavorBridge.sectorHomEquiv up down) f

theorem reconstruction_commutes (q : Residual U D up down) :
    (equiv U D up down).symm q = (DeltaBTwoFlavorBridge.sectorHomEquiv up down).symm
      (comparison U D up down q) := by
  unfold comparison
  exact LinearEquivComparison.reconstruction (equiv U D up down)
    (DeltaBTwoFlavorBridge.sectorHomEquiv up down) q

theorem reconstruct_extract (f : DeltaBTwoModelInterface.ModelSector up down) :
    (equiv U D up down).symm (equiv U D up down f) = f :=
  (equiv U D up down).symm_apply_apply f
theorem extract_reconstruct (q : Residual U D up down) :
    equiv U D up down ((equiv U D up down).symm q) = q :=
  (equiv U D up down).apply_symm_apply q

theorem forbidden_iff : (∀ f : DeltaBTwoModelInterface.ModelSector up down, f = 0) ↔
    ∀ q : Residual U D up down, q = 0 := by
  exact LinearEquivComparison.forbidden (equiv U D up down)

theorem nonzero_iff : (∃ f : DeltaBTwoModelInterface.ModelSector up down, f ≠ 0) ↔
    ∃ q : Residual U D up down, q ≠ 0 := by
  exact LinearEquivComparison.nonzero (equiv U D up down)

def oneGenerationEquiv : Residual ℂ ℂ DeltaBTwoFlavorOneGeneration.scalar
    DeltaBTwoFlavorOneGeneration.scalar ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (equiv ℂ ℂ DeltaBTwoFlavorOneGeneration.scalar DeltaBTwoFlavorOneGeneration.scalar).symm.trans
    DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv

end
end Physics.GradedSixQuarkComparison
