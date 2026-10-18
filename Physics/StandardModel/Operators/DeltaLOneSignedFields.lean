import Physics.StandardModel.Operators.DeltaLOneSignedInput
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Physics.FieldTheory.Spinor.OddWeylInvariant
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Math

/-! Standard typed gauge/Weyl carriers for the ten signed species. Negative
gauge charges use the contragredient unitary gauge representation; Weyl
chirality is reversed separately. Residual multiplicities remain explicit
model inputs, not silently identified with dual or conjugate modules. -/
namespace GUT.DeltaLOneSignedFields
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor SMEpsilonTensor
open DeltaLOneSignedInput
open scoped TensorProduct

abbrev GaugeCarrier : Species → Type
  | 0 => Quark
  | 1 => Color
  | 2 => Color
  | 3 => Weak
  | 4 => ℂ
  | 5 => Module.Dual ℂ Quark
  | 6 => Module.Dual ℂ Color
  | 7 => Module.Dual ℂ Color
  | 8 => Module.Dual ℂ Weak
  | 9 => Module.Dual ℂ ℂ

instance (s : Species) : AddCommGroup (GaugeCarrier s) := match s with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance
instance (s : Species) : Module ℂ (GaugeCarrier s) := match s with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance

abbrev gauge (s : Species) : Representation ℂ GaugeGroup (GaugeCarrier s) := match s with
  | 0 => quark
  | 1 => upRight
  | 2 => downRight
  | 3 => StandardSMGaugeTensor.lepton
  | 4 => electronRight
  | 5 => quark.dual
  | 6 => upRight.dual
  | 7 => downRight.dual
  | 8 => StandardSMGaugeTensor.lepton.dual
  | 9 => electronRight.dual

def rightHanded : Species → Bool := ![false,true,true,false,true,true,false,false,true,false]
def localField (s : Species) := external (gauge s) (FourSameWeylCompleteness.action (rightHanded s))

def hyperchargeElement (z : Circle) : GaugeGroup := (1,(1,z))

private theorem twist_hypercharge {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (w : ℤ)
    (ha : ∀ z x, a (hyperchargeElement z) x = x) (z : Circle) (x : A) :
    twist a w (hyperchargeElement z) x = (z : ℂ) ^ w • x := by
  change phase w (hyperchargeElement z) • a (hyperchargeElement z) x = _
  rw [ha]
  rfl

private theorem color_hypercharge (z : Circle) (x : Color) :
    color (hyperchargeElement z) x = x := by
  simp [color, hyperchargeElement, Matrix.toLin'_one]
private theorem weak_hypercharge (z : Circle) (x : Weak) :
    weak (hyperchargeElement z) x = x := by
  simp [weak, hyperchargeElement, Matrix.toLin'_one]
private theorem quark_hypercharge (z : Circle) (x : Quark) :
    (color.tprod weak) (hyperchargeElement z) x = x := by
  have h : (color.tprod weak) (hyperchargeElement z) = LinearMap.id := by
    ext a b
    simp [Representation.tprod_apply, color_hypercharge, weak_hypercharge]
  rw [h]; rfl

private theorem dual_weight {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (w : ℤ)
    (ha : ∀ z x, a (hyperchargeElement z) x = (z : ℂ) ^ w • x)
    (z : Circle) (f : Module.Dual ℂ A) :
    a.dual (hyperchargeElement z) f = (z : ℂ) ^ (-w) • f := by
  ext x
  change f (a (hyperchargeElement z)⁻¹ x) = (z : ℂ) ^ (-w) * f x
  have hi : (hyperchargeElement z)⁻¹ = hyperchargeElement z⁻¹ := by
    simp [hyperchargeElement]
  rw [hi, ha, map_smul, smul_eq_mul]
  simp

theorem gauge_hypercharge (z : Circle) (s : Species) (x : GaugeCarrier s) :
    gauge s (hyperchargeElement z) x = (z : ℂ) ^ hypercharge s • x := by
  fin_cases s
  · exact twist_hypercharge _ 1 quark_hypercharge z x
  · exact twist_hypercharge _ 4 color_hypercharge z x
  · exact twist_hypercharge _ (-2) color_hypercharge z x
  · exact twist_hypercharge _ (-3) weak_hypercharge z x
  · exact twist_hypercharge _ (-6) (by intro z x; rfl) z x
  · exact dual_weight quark 1 (twist_hypercharge _ 1 quark_hypercharge) z x
  · exact dual_weight upRight 4 (twist_hypercharge _ 4 color_hypercharge) z x
  · simpa [gauge, hypercharge] using
      dual_weight downRight (-2) (twist_hypercharge _ (-2) color_hypercharge) z x
  · simpa [gauge, hypercharge] using dual_weight StandardSMGaugeTensor.lepton (-3)
      (twist_hypercharge _ (-3) weak_hypercharge) z x
  · simpa [gauge, hypercharge] using dual_weight electronRight (-6)
      (twist_hypercharge _ (-6) (by intro z x; rfl)) z x

def colorCenter (z : Circle) (hz : z ^ 3 = 1) : Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal (fun _ => (z : ℂ)), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst j
        simp [← Circle.coe_inv_eq_conj, z.coe_ne_zero]
      · simp [h]
    · rw [Matrix.det_diagonal]
      have hp : (z : ℂ) ^ 3 = 1 := congrArg (fun x : Circle => (x : ℂ)) hz
      simpa [Fin.prod_univ_succ, pow_succ] using hp⟩

def centerElement (z : Circle) (hz : z ^ 3 = 1) : GaugeGroup := (colorCenter z hz,(1,1))

private theorem color_center (z : Circle) (hz : z ^ 3 = 1) (x : Color) :
    color (centerElement z hz) x = (z : ℂ) • x := by
  ext i
  simp [color, centerElement, colorCenter, Matrix.toLin'_apply, Matrix.mulVec]

private theorem weak_center (z : Circle) (hz : z ^ 3 = 1) (x : Weak) :
    weak (centerElement z hz) x = x := by
  simp [weak, centerElement, Matrix.toLin'_one]

private theorem twist_center {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (w : ℤ) (z : Circle) (hz : z ^ 3 = 1) (x : A) :
    twist a w (centerElement z hz) x = a (centerElement z hz) x := by
  change phase w (centerElement z hz) • a (centerElement z hz) x = a (centerElement z hz) x
  simp [phase, centerElement]

private theorem quark_center (z : Circle) (hz : z ^ 3 = 1) (x : Quark) :
    quark (centerElement z hz) x = (z : ℂ) • x := by
  rw [quark, twist_center]
  have h : (color.tprod weak) (centerElement z hz) = (z : ℂ) • LinearMap.id := by
    ext a b
    simp [Representation.tprod_apply, color_center, weak_center, TensorProduct.smul_tmul]
  rw [h]; rfl

private theorem dual_scalar {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (g : GaugeGroup) (c : ℂ) (hc : c ≠ 0)
    (ha : ∀ x, a g x = c • x) (f : Module.Dual ℂ A) : a.dual g f = c⁻¹ • f := by
  have hinv (x : A) : a g⁻¹ x = c⁻¹ • x := by
    have h : a g (a g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [ha] at h
    have h' := congrArg (fun v => c⁻¹ • v) h
    simpa [smul_smul, hc] using h'
  ext x
  change f (a g⁻¹ x) = c⁻¹ * f x
  rw [hinv, map_smul, smul_eq_mul]

theorem gauge_center (z : Circle) (hz : z ^ 3 = 1) (s : Species) (x : GaugeCarrier s) :
    gauge s (centerElement z hz) x = (z : ℂ) ^ baryon s • x := by
  fin_cases s <;> simp [baryon]
  · exact quark_center z hz x
  · change twist color 4 _ x = (z : ℂ) • x
    rw [twist_center, color_center]
  · change twist color (-2) _ x = (z : ℂ) • x
    rw [twist_center, color_center]
  · change twist weak (-3) _ x = x
    rw [twist_center, weak_center]
  · change twist (Representation.trivial ℂ GaugeGroup ℂ) (-6) _ x = x
    rw [twist_center]; rfl
  · simpa [baryon] using dual_scalar quark (centerElement z hz) z z.coe_ne_zero
      (quark_center z hz) x
  · simpa [baryon] using dual_scalar upRight (centerElement z hz) z z.coe_ne_zero
      (by intro x; change twist color 4 _ x = _; rw [twist_center, color_center]) x
  · simpa [baryon] using dual_scalar downRight (centerElement z hz) z z.coe_ne_zero
      (by intro x; change twist color (-2) _ x = _; rw [twist_center, color_center]) x
  · simpa [baryon] using dual_scalar StandardSMGaugeTensor.lepton (centerElement z hz) 1
      one_ne_zero (by
        intro x
        change twist weak (-3) _ x = (1 : ℂ) • x
        rw [twist_center, weak_center, one_smul]) x
  · simpa [baryon] using dual_scalar electronRight (centerElement z hz) 1 one_ne_zero
      (by
        intro x
        change twist (Representation.trivial ℂ GaugeGroup ℂ) (-6) _ x = (1 : ℂ) • x
        rw [twist_center]
        exact (one_smul ℂ x).symm) x

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

abbrev Field (s : Species) := (GaugeCarrier s ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] F s
@[reducible] instance (s : Species) : AddCommGroup (Field (F := F) s) :=
  TensorProduct.addCommGroup
def field (s : Species) := external (localField s) (flavor s)
def fullRepresentation := FiniteSpeciesExterior.representation (field flavor)
abbrev Sector (degree : ℤ) := DeltaLOneSignedInput.sector (field flavor) degree
def fullHypercharge (z : Circle) : (GaugeGroup × WeylSpinor.Group) × R :=
  ((hyperchargeElement z,1),1)

def fullSpinTest : (GaugeGroup × WeylSpinor.Group) × R := ((1,OddWeylInvariant.testElement),1)

theorem field_spin_basis (s : Species) (a : GaugeCarrier s) (i : Fin 2) (x : F s) :
    field flavor s fullSpinTest ((a ⊗ₜ[ℂ] weakBasis i) ⊗ₜ[ℂ] x) =
      OddWeylInvariant.slotEigen (rightHanded s) i • ((a ⊗ₜ[ℂ] weakBasis i) ⊗ₜ[ℂ] x) := by
  simp [field, localField, external, fullSpinTest, Representation.tprod_apply,
    OddWeylInvariant.test_basis, TensorProduct.tmul_smul, TensorProduct.smul_tmul]

theorem leftSlots_counts (labels : Fin 4 → Species) :
    DeltaLOneSpeciesSupport.leftSlots (counts labels) =
      ∑ i, if rightHanded (labels i) then 0 else 1 := by
  rw [DeltaLOneSignedInput.sum_weights labels (fun s => if rightHanded s then (0 : ℕ) else 1)]
  simp [DeltaLOneSpeciesSupport.leftSlots, counts, rightHanded, Fin.sum_univ_succ, add_assoc]

theorem odd_basis_vanish (f : DeltaLOneSignedInput.Coefficient (field flavor))
    (labels : Fin 4 → Species)
    (hodd : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 1)
    (a : ∀ i, GaugeCarrier (labels i)) (idx : Fin 4 → Fin 2) (x : ∀ i, F (labels i)) :
    FiniteSpeciesExterior.restrict (field flavor) f labels
      (fun i => (a i ⊗ₜ[ℂ] weakBasis (idx i)) ⊗ₜ[ℂ] x i) = 0 := by
  have hp := OddWeylInvariant.odd_product_ne_one
    (rightHanded (labels 0)) (rightHanded (labels 1))
    (rightHanded (labels 2)) (rightHanded (labels 3))
    (by simpa [leftSlots_counts, Fin.sum_univ_succ, add_assoc] using hodd)
    (idx 0) (idx 1) (idx 2) (idx 3)
  apply ExteriorWeightSupport.vanish_of_scalar (FiniteSpeciesExterior.representation (field flavor))
    f fullSpinTest _ (fun i => OddWeylInvariant.slotEigen (rightHanded (labels i)) (idx i))
  · intro i
    change FiniteSpeciesExterior.representation (field flavor) fullSpinTest
      (Pi.single (labels i) ((a i ⊗ₜ[ℂ] weakBasis (idx i)) ⊗ₜ[ℂ] x i)) =
      OddWeylInvariant.slotEigen (rightHanded (labels i)) (idx i) •
        Pi.single (labels i) ((a i ⊗ₜ[ℂ] weakBasis (idx i)) ⊗ₜ[ℂ] x i)
    rw [FiniteSpeciesExterior.action_single, field_spin_basis]
    exact Pi.single_smul _ _ _
  · have hprod : (∏ i, OddWeylInvariant.slotEigen (rightHanded (labels i)) (idx i)) - 1 ≠ 0 := by
      convert hp using 1; simp [Fin.prod_univ_succ, mul_assoc]
    exact sub_ne_zero.mp hprod

theorem odd_restriction_vanish (f : DeltaLOneSignedInput.Coefficient (field flavor))
    (labels : Fin 4 → Species)
    (hodd : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 1) :
    FiniteSpeciesExterior.restrict (field flavor) f labels = 0 := by
  let b := fun i : Fin 4 =>
    ((Module.Free.chooseBasis ℂ (GaugeCarrier (labels i))).tensorProduct
      (Pi.basisFun ℂ (Fin 2))).tensorProduct (Module.Free.chooseBasis ℂ (F (labels i)))
  apply Module.Basis.ext_multilinear b
  intro v
  simpa only [b, Module.Basis.tensorProduct_apply', Pi.basisFun_apply, weakBasis, zero_apply] using
    odd_basis_vanish flavor f labels hodd
      (fun i => Module.Free.chooseBasis ℂ (GaugeCarrier (labels i)) (v i).1.1)
      (fun i => (v i).1.2)
      (fun i => Module.Free.chooseBasis ℂ (F (labels i)) (v i).2)
theorem field_hypercharge (z : Circle) (s : Species) (x : Field (F := F) s) :
    field flavor s (fullHypercharge z) x = (z : ℂ) ^ hypercharge s • x := by
  have h : field flavor s (fullHypercharge z) =
      (z : ℂ) ^ hypercharge s • LinearMap.id := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro b
    simp [field, localField, external, fullHypercharge, Representation.tprod_apply,
      gauge_hypercharge, TensorProduct.smul_tmul]
  rw [h]; rfl

/-- Hypercharge neutrality now follows on the full standard signed-field
input, with no character assumptions on an unknown coefficient. -/
theorem hypercharge_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.sixHypercharge (counts labels) = 0 :=
  DeltaLOneSignedInput.hypercharge_of_nonzero (field flavor) f.val labels v
    fullHypercharge (field_hypercharge flavor) hf

def fullCenter (z : Circle) (hz : z ^ 3 = 1) : (GaugeGroup × WeylSpinor.Group) × R :=
  ((centerElement z hz,1),1)

theorem field_center (z : Circle) (hz : z ^ 3 = 1) (s : Species) (x : Field (F := F) s) :
    field flavor s (fullCenter z hz) x = (z : ℂ) ^ baryon s • x := by
  have h : field flavor s (fullCenter z hz) = (z : ℂ) ^ baryon s • LinearMap.id := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro b
    simp [field, localField, external, fullCenter, Representation.tprod_apply,
      gauge_center, TensorProduct.smul_tmul]
  rw [h]; rfl

def trialityRoot : Circle := Circle.exp (2 * Real.pi / 3)
theorem trialityRoot_primitive : IsPrimitiveRoot trialityRoot 3 := by
  apply IsPrimitiveRoot.of_map_of_injective (f := Circle.coeHom) (hf := Subtype.coe_injective)
  change IsPrimitiveRoot (trialityRoot : ℂ) 3
  have he : (trialityRoot : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 3) := by
    rw [trialityRoot, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp 3 (by decide)

theorem triality_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.threeBaryonDegree (counts labels) % 3 = 0 :=
  DeltaLOneSignedInput.triality_of_nonzero (field flavor) f.val labels v trialityRoot
    trialityRoot_primitive (fullCenter trialityRoot trialityRoot_primitive.pow_eq_one)
    (field_center flavor trialityRoot trialityRoot_primitive.pow_eq_one) hf

/-- Six supports, now for actual standard signed-field actions. -/
theorem gauge_candidates (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    counts labels = DeltaLOneSpeciesSupport.duql ∨ counts labels = DeltaLOneSpeciesSupport.qque ∨
      counts labels = DeltaLOneSpeciesSupport.qqql ∨ counts labels = DeltaLOneSpeciesSupport.duue ∨
      counts labels = DeltaLOneSpeciesSupport.antiQddL ∨
      counts labels = DeltaLOneSpeciesSupport.antiDddE := by
  apply (DeltaLOneSpeciesSupport.gauge_admissible_iff _).mp
  exact ⟨slotCount_counts labels, DeltaLOneSignedInput.lepton_of_nonzero _ f labels v hf,
    hypercharge_of_nonzero flavor f labels v hf, triality_of_nonzero flavor f labels v hf⟩

/-- Weyl parity is necessary on every species ordering, including spectators. -/
theorem even_leftSlots_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 0 := by
  by_contra h
  have ho : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 1 := by omega
  exact hf (by rw [odd_restriction_vanish flavor f.val labels ho]; rfl)

theorem admissible_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.Admissible (counts labels) :=
  ⟨slotCount_counts labels, DeltaLOneSignedInput.lepton_of_nonzero _ f labels v hf,
    hypercharge_of_nonzero flavor f labels v hf, triality_of_nonzero flavor f labels v hf,
    even_leftSlots_of_nonzero flavor f labels v hf⟩

/-- No support predicate is imposed on the input: invariance derives the four families. -/
theorem four_candidates (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    counts labels = DeltaLOneSpeciesSupport.duql ∨ counts labels = DeltaLOneSpeciesSupport.qque ∨
      counts labels = DeltaLOneSpeciesSupport.qqql ∨ counts labels = DeltaLOneSpeciesSupport.duue :=
  (DeltaLOneSpeciesSupport.admissible_iff _).mp (admissible_of_nonzero flavor f labels v hf)

theorem vanish_outside_four (f : Sector flavor 1) (labels : Fin 4 → Species)
    (h : ¬ (counts labels = DeltaLOneSpeciesSupport.duql ∨
      counts labels = DeltaLOneSpeciesSupport.qque ∨ counts labels = DeltaLOneSpeciesSupport.qqql ∨
      counts labels = DeltaLOneSpeciesSupport.duue)) :
    FiniteSpeciesExterior.restrict (field flavor) f.val labels = 0 := by
  ext v
  by_contra hv
  exact h (four_candidates flavor f labels v hv)

theorem baryonDegree_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.threeBaryonDegree (counts labels) = 3 :=
  DeltaLOneSpeciesSupport.baryonDegree_of_admissible _ (admissible_of_nonzero flavor f labels v hf)

theorem no_conjugates_of_nonzero (f : Sector flavor 1) (labels : Fin 4 → Species)
    (v : ∀ i, Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (field flavor) f.val labels v ≠ 0) :
    (counts labels).cq + (counts labels).cu + (counts labels).cd +
      (counts labels).cl + (counts labels).ce = 0 :=
  DeltaLOneSpeciesSupport.no_conjugates _ (admissible_of_nonzero flavor f labels v hf)

end
end GUT.DeltaLOneSignedFields
