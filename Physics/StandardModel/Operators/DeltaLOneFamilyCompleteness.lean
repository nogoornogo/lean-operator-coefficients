import Physics.StandardModel.Operators.DeltaLOneFourFamilyDecomposition
import Physics.StandardModel.Operators.DuqlExteriorCompleteness
import Physics.StandardModel.Operators.QquePhysicalExteriorCompleteness
import Physics.StandardModel.Operators.QqqlExteriorCompleteness
import Physics.StandardModel.Operators.DuueResidualCompleteness
import Math.RepresentationTheory.SpeciesPatternAssembly

open Math

/-! Connect the intrinsic family summands to their existing ordered and residual
classifications. Repeated-species normalizations are handled before this step. -/
namespace GUT.DeltaLOneFamilyCompleteness
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneSignedFields DeltaLOneFourFamilyDecomposition
open SpeciesPatternAssembly
open scoped TensorProduct
variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

local instance : AddCommGroup (((SMEpsilonTensor.Color ⊗[ℂ] SMEpsilonTensor.Weak)
    ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] F 0) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 1) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Color ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 2) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((SMEpsilonTensor.Weak ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 3) := Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space)
    ⊗[ℂ] F 4) := Module.addCommMonoidToAddCommGroup ℂ

abbrev PatternMaps (i : Fin 4) := MultilinearInvariantHom.invariantMaps (W := ℂ)
  (fun j => field flavor (pattern i j))
abbrev PatternSpace (i : Fin 4) := orderedSpace (field flavor) (pattern i)

def patternEquiv (i : Fin 4) : FamilySector flavor i ≃ₗ[ℂ] PatternSpace flavor i :=
  SpeciesPatternAssembly.equiv (field flavor) (pattern i) (familySupport i)
    (stable i) (orbit i) (counts_pattern i)

def duqlTensor : PatternMaps flavor 0 ≃ₗ[ℂ]
    DuqlOrderedCompleteness.Coefficient (flavor 2) (flavor 1) (flavor 0) (flavor 3) :=
  FourTensorMultilinear.invariantEquiv _

def qqueTensor : PatternMaps flavor 1 ≃ₗ[ℂ]
    QquePhysicalOrderedCompleteness.Coefficient (flavor 0) (flavor 1) (flavor 4) :=
  FourTensorMultilinear.invariantEquiv _

def qqqlTensor : PatternMaps flavor 2 ≃ₗ[ℂ]
    QqqlOrderedCompleteness.Coefficient (flavor 0) (flavor 3) :=
  FourTensorMultilinear.invariantEquiv _

def duueTensor : PatternMaps flavor 3 ≃ₗ[ℂ]
    DuueOrderedCompleteness.Coefficient (flavor 1) (flavor 2) (flavor 4) :=
  FourTensorMultilinear.invariantEquiv _

theorem duql_fixing : ∀ p : Equiv.Perm (Fin 4), pattern 0 ∘ p = pattern 0 → p = 1 := by
  decide +kernel

theorem repeated_fixing (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    ∀ p : Equiv.Perm (Fin 4), pattern i ∘ p = pattern i ↔
      p = 1 ∨ p = Equiv.swap 0 1 := by
  rcases hi with rfl | rfl <;> decide +kernel

theorem triple_fixing : ∀ p : Equiv.Perm (Fin 4), pattern 2 ∘ p = pattern 2 ↔ p 3 = 3 := by
  decide +kernel

theorem duql_compatible (k : PatternMaps flavor 0) : Compatible (V := Field (F := F)) (pattern 0) k.val := by
  intro p hp w
  rw [duql_fixing p hp]
  simp

def duqlOrderedEquiv : PatternSpace flavor 0 ≃ₗ[ℂ]
    DuqlOrderedCompleteness.Coefficient (flavor 2) (flavor 1) (flavor 0) (flavor 3) where
  toFun k := duqlTensor flavor k.val
  invFun f := ⟨(duqlTensor flavor).symm f, duql_compatible flavor _⟩
  left_inv k := by apply Subtype.ext; exact (duqlTensor flavor).symm_apply_apply k.val
  right_inv f := (duqlTensor flavor).apply_symm_apply f
  map_add' k l := (duqlTensor flavor).map_add k.val l.val
  map_smul' z k := (duqlTensor flavor).map_smul z k.val

theorem pair_compatible_iff (i : Fin 4) (hi : i = 1 ∨ i = 3) (k : PatternMaps flavor i) :
    Compatible (V := Field (F := F)) (pattern i) k.val ↔
      ∀ w : Fin 4 → ∀ s, Field (F := F) s,
        ordered (pattern i) k.val (w ∘ Equiv.swap 0 1) = -ordered (pattern i) k.val w := by
  constructor
  · intro hk w
    have he := hk (Equiv.swap 0 1) ((repeated_fixing i hi _).mpr (Or.inr rfl)) w
    have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 := by decide
    rw [hn] at he
    exact neg_eq_iff_eq_neg.mp (by simpa using he)
  · intro hk p hp w
    rcases (repeated_fixing i hi p).mp hp with rfl | rfl
    · simp
    · have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 := by decide
      rw [hn, hk]
      simp

theorem qque_ordered_apply (f : QquePhysicalOrderedCompleteness.Coefficient
    (flavor 0) (flavor 1) (flavor 4)) (w : Fin 4 → ∀ s, Field (F := F) s) :
    ordered (pattern 1) ((qqueTensor flavor).symm f).val w =
      f (((w 0 0 ⊗ₜ[ℂ] w 1 0) ⊗ₜ[ℂ] (w 2 1 ⊗ₜ[ℂ] w 3 4))) := rfl

theorem duue_ordered_apply (f : DuueOrderedCompleteness.Coefficient
    (flavor 1) (flavor 2) (flavor 4)) (w : Fin 4 → ∀ s, Field (F := F) s) :
    ordered (pattern 3) ((duueTensor flavor).symm f).val w =
      f (((w 0 1 ⊗ₜ[ℂ] w 1 1) ⊗ₜ[ℂ] (w 2 2 ⊗ₜ[ℂ] w 3 4))) := rfl

theorem qqql_ordered_apply (f : QqqlOrderedCompleteness.Coefficient
    (flavor 0) (flavor 3)) (w : Fin 4 → ∀ s, Field (F := F) s) :
    ordered (pattern 2) ((qqqlTensor flavor).symm f).val w =
      f (((w 0 0 ⊗ₜ[ℂ] w 1 0) ⊗ₜ[ℂ] (w 2 0 ⊗ₜ[ℂ] w 3 3))) := rfl

theorem qque_compatible_iff (f : QquePhysicalOrderedCompleteness.Coefficient
    (flavor 0) (flavor 1) (flavor 4)) :
    Compatible (V := Field (F := F)) (pattern 1) ((qqueTensor flavor).symm f).val ↔
      f ∈ QquePhysicalExteriorCompleteness.OrderedSector (flavor 0) (flavor 1) (flavor 4) := by
  rw [pair_compatible_iff flavor 1 (Or.inl rfl)]
  constructor
  · intro hk x y u e
    have he := hk ![Pi.single 0 x, Pi.single 0 y, Pi.single 1 u, Pi.single 4 e]
    simp only [qque_ordered_apply] at he
    simp [Function.comp_apply, Equiv.swap_apply_def] at he
    exact he
  · intro hf w
    exact hf (w 0 0) (w 1 0) (w 2 1) (w 3 4)

def qqueOrderedEquiv : PatternSpace flavor 1 ≃ₗ[ℂ]
    QquePhysicalExteriorCompleteness.OrderedSector (flavor 0) (flavor 1) (flavor 4) where
  toFun k := ⟨qqueTensor flavor k.val, (qque_compatible_iff flavor _).mp
    (by rw [(qqueTensor flavor).symm_apply_apply]; exact k.property)⟩
  invFun f := ⟨(qqueTensor flavor).symm f.val, (qque_compatible_iff flavor f.val).mpr f.property⟩
  left_inv k := by apply Subtype.ext; exact (qqueTensor flavor).symm_apply_apply k.val
  right_inv f := by apply Subtype.ext; exact (qqueTensor flavor).apply_symm_apply f.val
  map_add' k l := by apply Subtype.ext; exact (qqueTensor flavor).map_add k.val l.val
  map_smul' z k := by apply Subtype.ext; exact (qqueTensor flavor).map_smul z k.val

theorem duue_compatible_iff (f : DuueOrderedCompleteness.Coefficient
    (flavor 1) (flavor 2) (flavor 4)) :
    Compatible (V := Field (F := F)) (pattern 3) ((duueTensor flavor).symm f).val ↔
      f ∈ DuueExchange.OrderedSector (flavor 1) (flavor 2) (flavor 4) := by
  rw [pair_compatible_iff flavor 3 (Or.inr rfl)]
  constructor
  · intro hk x y d e
    have he := hk ![Pi.single 1 x, Pi.single 1 y, Pi.single 2 d, Pi.single 4 e]
    simp only [duue_ordered_apply] at he
    simp [Function.comp_apply, Equiv.swap_apply_def] at he
    exact he
  · intro hf w
    exact hf (w 0 1) (w 1 1) (w 2 2) (w 3 4)

def duueOrderedEquiv : PatternSpace flavor 3 ≃ₗ[ℂ]
    DuueExchange.OrderedSector (flavor 1) (flavor 2) (flavor 4) where
  toFun k := ⟨duueTensor flavor k.val, (duue_compatible_iff flavor _).mp
    (by rw [(duueTensor flavor).symm_apply_apply]; exact k.property)⟩
  invFun f := ⟨(duueTensor flavor).symm f.val, (duue_compatible_iff flavor f.val).mpr f.property⟩
  left_inv k := by apply Subtype.ext; exact (duueTensor flavor).symm_apply_apply k.val
  right_inv f := by apply Subtype.ext; exact (duueTensor flavor).apply_symm_apply f.val
  map_add' k l := by apply Subtype.ext; exact (duueTensor flavor).map_add k.val l.val
  map_smul' z k := by apply Subtype.ext; exact (duueTensor flavor).map_smul z k.val

theorem triple_permutation : ∀ p : Equiv.Perm (Fin 4), p 3 = 3 →
    p = 1 ∨ p = Equiv.swap 0 1 ∨ p = Equiv.swap 1 2 ∨
      p = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ p = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
      p = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide +kernel

theorem qqql_compatible_iff (f : QqqlOrderedCompleteness.Coefficient (flavor 0) (flavor 3)) :
    Compatible (V := Field (F := F)) (pattern 2) ((qqqlTensor flavor).symm f).val ↔
      f ∈ QqqlExteriorCompleteness.OrderedSector (flavor 0) (flavor 3) := by
  change _ ↔ FourSlotTripleAlternation.Alternates f.toLinearMap
  rw [FourSlotTripleAlternation.alternates_iff_adjacent]
  constructor
  · intro hk
    constructor
    · intro x y z l
      have he := hk (Equiv.swap 0 1) ((triple_fixing _).mpr (by decide))
        ![Pi.single 0 x, Pi.single 0 y, Pi.single 0 z, Pi.single 3 l]
      have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 := by decide
      rw [hn] at he
      simp only [qqql_ordered_apply] at he
      simp [Function.comp_apply, Equiv.swap_apply_def] at he
      exact neg_eq_iff_eq_neg.mp he
    · intro x y z l
      have he := hk (Equiv.swap 1 2) ((triple_fixing _).mpr (by decide))
        ![Pi.single 0 x, Pi.single 0 y, Pi.single 0 z, Pi.single 3 l]
      have hn : Equiv.Perm.sign (Equiv.swap (1 : Fin 4) 2) = -1 := by decide
      rw [hn] at he
      simp only [qqql_ordered_apply] at he
      simp [Function.comp_apply, Equiv.swap_apply_def] at he
      exact neg_eq_iff_eq_neg.mp he
  · rintro ⟨h01,h12⟩ p hp w
    change ∀ x y z l, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] l)) =
      -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] l)) at h01
    change ∀ x y z l, f ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] l)) =
      -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] l)) at h12
    rcases triple_permutation p ((triple_fixing p).mp hp) with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [qqql_ordered_apply]
    all_goals simp [Function.comp_apply, Equiv.swap_apply_def]
    all_goals grind only

def qqqlOrderedEquiv : PatternSpace flavor 2 ≃ₗ[ℂ]
    QqqlExteriorCompleteness.OrderedSector (flavor 0) (flavor 3) where
  toFun k := ⟨qqqlTensor flavor k.val, (qqql_compatible_iff flavor _).mp
    (by rw [(qqqlTensor flavor).symm_apply_apply]; exact k.property)⟩
  invFun f := ⟨(qqqlTensor flavor).symm f.val, (qqql_compatible_iff flavor f.val).mpr f.property⟩
  left_inv k := by apply Subtype.ext; exact (qqqlTensor flavor).symm_apply_apply k.val
  right_inv f := by apply Subtype.ext; exact (qqqlTensor flavor).apply_symm_apply f.val
  map_add' k l := by apply Subtype.ext; exact (qqqlTensor flavor).map_add k.val l.val
  map_smul' z k := by apply Subtype.ext; exact (qqqlTensor flavor).map_smul z k.val

/-- The distinct-species family has one unrestricted residual intertwiner. -/
def duqlEquiv : FamilySector flavor 0 ≃ₗ[ℂ]
    DuqlOrderedCompleteness.Residual (flavor 2) (flavor 1) (flavor 0) (flavor 3) :=
  (patternEquiv flavor 0).trans ((duqlOrderedEquiv flavor).trans
    (StatisticalCompleteness.noExchanges (DuqlOrderedCompleteness.homEquiv _ _ _ _)))

theorem duqlEquiv_agrees : duqlEquiv flavor =
    (patternEquiv flavor 0).trans ((duqlOrderedEquiv flavor).trans
      (DuqlOrderedCompleteness.homEquiv _ _ _ _)) := by
  rw [duqlEquiv, StatisticalCompleteness.noExchanges_agrees]

/-- The two quark flavors obey the proved symmetric residual relation. -/
def qqueEquiv : FamilySector flavor 1 ≃ₗ[ℂ]
    QquePhysicalExteriorCompleteness.residualSpace (flavor 0) (flavor 1) (flavor 4) :=
  (patternEquiv flavor 1).trans ((qqueOrderedEquiv flavor).trans
    (QquePhysicalExteriorCompleteness.orderedEquiv _ _ _))

/-- All weak and Lorentz conditions have been removed; only finite residual
exchange equations remain. -/
def qqqlEquiv : FamilySector flavor 2 ≃ₗ[ℂ]
    QqqlExchange.residualSpace (flavor 0) (flavor 3) :=
  (patternEquiv flavor 2).trans ((qqqlOrderedEquiv flavor).trans
    (QqqlExteriorCompleteness.orderedEquiv _ _))

/-- Solving repeated-up exchange leaves one unrestricted residual intertwiner. -/
def duueEquiv : FamilySector flavor 3 ≃ₗ[ℂ]
    DuueOrderedCompleteness.Residual (flavor 1) (flavor 2) (flavor 4) :=
  (patternEquiv flavor 3).trans ((duueOrderedEquiv flavor).trans
    ((DuueExchange.orderedEquiv _ _ _).trans
      (DuueResidualCompleteness.residualEquiv _ _ _)))

/-- Canonical probes divide alternatization by precisely the stabilizer size. -/
theorem stabilizer_card : ∀ i : Fin 4,
    (SpeciesPatternAssembly.stabilizer (pattern i)).card = ![1,2,6,2] i := by
  decide +kernel

end
end GUT.DeltaLOneFamilyCompleteness
