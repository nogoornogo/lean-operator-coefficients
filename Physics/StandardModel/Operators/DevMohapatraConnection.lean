import Physics.StandardModel.Operators.DevMohapatraSixQuark
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.SixQuarkConventionalBasis
import Math.RepresentationTheory.SixSlotSpeciesSum

namespace GUT.DevMohapatraConnection
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open Math Representation SixQuarkInvariant SMEpsilonTensor
open scoped TensorProduct
abbrev F := DevMohapatraSixQuark.F
abbrev H := DevMohapatraSixQuark.H
abbrev residual := DevMohapatraSixQuark.residual

/-- Actual reordered right-quark action, including hypercharge and weak neutrality. -/
def action (g : DeltaBTwoModelInterface.SymmetryGroup H) (i : Fin 6) :
    Quark ⊗[ℂ] F →ₗ[ℂ] Quark ⊗[ℂ] F :=
  StandardSMGaugeTensor.phase (DeltaBTwoFlavorBridge.charge i) g.1.1 •
    TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (residual g.1.2)

theorem physical_invariant (f : DevMohapatraSixQuark.Sector)
    (g : DeltaBTwoModelInterface.SymmetryGroup H) (v : Fin 6 → Quark ⊗[ℂ] F) :
    f.val (fun i => action g i (v i)) = f.val v := by
  change f.val (fun i => StandardSMGaugeTensor.phase (DeltaBTwoFlavorBridge.charge i) g.1.1 •
    TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (residual g.1.2) (v i)) = _
  rw [f.val.map_smul_univ, DeltaBTwoFlavorBridge.phase_product, one_smul]
  have hs : TensorProduct.map ((colorAction g.1.1.1).comp (spinAction g.2)) (residual g.1.2) =
      (TensorProduct.map (colorAction g.1.1.1) (LinearMap.id : F →ₗ[ℂ] F)).comp
        ((TensorProduct.map (spinAction g.2) (LinearMap.id : F →ₗ[ℂ] F)).comp
          (TensorProduct.map LinearMap.id (residual g.1.2))) := by
    apply TensorProduct.ext
    ext q t
    simp
  simp_rw [hs, LinearMap.comp_apply]
  rw [f.property.1.1, f.property.1.2, f.property.2.1]

theorem up_action (g : DeltaBTwoModelInterface.SymmetryGroup H)
    (v : (Color ⊗[ℂ] F) ⊗[ℂ] Spin) :
    DeltaBTwoFlavorBridge.reorder (DeltaBTwoModelInterface.upModel residual g v) =
      action g 0 (DeltaBTwoFlavorBridge.reorder v) :=
  DeltaBTwoFlavorBridge.reorder_up_action residual g v

theorem down_action (g : DeltaBTwoModelInterface.SymmetryGroup H)
    (v : (Color ⊗[ℂ] F) ⊗[ℂ] Spin) :
    DeltaBTwoFlavorBridge.reorder (DeltaBTwoModelInterface.downModel residual g v) =
      action g 1 (DeltaBTwoFlavorBridge.reorder v) :=
  DeltaBTwoFlavorBridge.reorder_down_action residual g v

/-- Literal Eq.(4) local contraction, with C-inverse read as right Weyl epsilon. -/
def spin : SixWeylMultilinear.Coefficient :=
  (SixWeylMultilinear.pairing 0).domDomCongr (Equiv.swap 1 2)

theorem spin_invariant : SixWeylMultilinear.IsInvariant spin := by
  intro g v
  exact SixWeylMultilinear.pairing_invariant 0 g (v ∘ Equiv.swap 1 2)

def printed : Coefficient := combine (SixColorInvariant.pairing 1) spin

theorem printed_invariant : IsInvariant printed :=
  SixQuarkConventionalBasis.combine_invariant _ _
    (SixColorInvariant.pairing_invariant 1) spin_invariant

theorem printed_apply (c : Fin 6 → Color) (s : Fin 6 → Spin) :
    printed (fun i => c i ⊗ₜ[ℂ] s i) =
    (eps3 (c 0) (c 1) (c 3) * eps3 (c 2) (c 4) (c 5)) *
      (eps2 (s 0) (s 2) * eps2 (s 1) (s 3) * eps2 (s 4) (s 5)) := by
  rw [printed, combine_apply]
  simp [spin, SixColorInvariant.pairingValue, SixWeylMultilinear.pairingValue,
    SixWeylInvariant.pairingValue, Equiv.swap_apply_def]
/-- Flavor projection selecting d or s in a quark-flavor tensor. -/
def project (j : Fin 2) : Quark ⊗[ℂ] F →ₗ[ℂ] Quark :=
  (TensorProduct.rid ℂ Quark).toLinearMap.comp
    (TensorProduct.map LinearMap.id (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j))

@[simp] theorem project_pure (j : Fin 2) (q : Quark) (t : F) :
    project j (q ⊗ₜ[ℂ] t) = t j • q := by simp [project]

def flavored : SixQuarkFlavorCoordinates.FlavorCoefficient (V := fun _ => F) :=
  printed.compLinearMap (fun i => project (DevMohapatraSixQuark.labels i))

theorem flavored_pure (q : Fin 6 → Quark) (t : Fin 6 → F) :
    flavored (fun i => q i ⊗ₜ[ℂ] t i) =
      (∏ i, t i (DevMohapatraSixQuark.labels i)) • printed q := by
  change printed (fun i => project _ (q i ⊗ₜ[ℂ] t i)) = _
  simp_rw [project_pure]
  exact printed.map_smul_univ _ _

theorem project_action (j : Fin 2) (g : DeltaBTwoModelInterface.SymmetryGroup H)
    (i : Fin 6) (v : Quark ⊗[ℂ] F) :
    project j (action g i v) =
      (StandardSMGaugeTensor.phase (DeltaBTwoFlavorBridge.charge i) g.1.1 *
        DevMohapatraSixQuark.phase g.1.2) •
        ((colorAction g.1.1.1).comp (spinAction g.2)) (project j v) := by
  have he : (project j).comp (action g i) =
      (StandardSMGaugeTensor.phase (DeltaBTwoFlavorBridge.charge i) g.1.1 *
        DevMohapatraSixQuark.phase g.1.2) •
        (((colorAction g.1.1.1).comp (spinAction g.2)).comp (project j)) := by
    apply TensorProduct.ext'
    intro q t
    simp [action, residual, DevMohapatraSixQuark.residual, DevMohapatraParity.copies,
      DevMohapatraSixQuark.phase, smul_smul, mul_comm]
  exact LinearMap.congr_fun he v

theorem flavored_invariant (g : DeltaBTwoModelInterface.SymmetryGroup H)
    (v : Fin 6 → Quark ⊗[ℂ] F) : flavored (fun i => action g i (v i)) = flavored v := by
  change printed (fun i => project _ (action g i (v i))) = printed (fun i => project _ (v i))
  simp_rw [project_action]
  rw [printed.map_smul_univ, Finset.prod_mul_distrib,
    DeltaBTwoFlavorBridge.phase_product]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    DevMohapatraSixQuark.phase_six, one_mul, one_smul, LinearMap.comp_apply]
  rw [printed_invariant.1, printed_invariant.2]

/-- Source's selected antisymmetric two-down-flavor coupling tensor. -/
def downCoupling (z : ℂ) (t u : F) : ℂ := z * (t 0 * u 1 - t 1 * u 0)

theorem downCoupling_swap (z : ℂ) (t u : F) :
    downCoupling z u t = -downCoupling z t u := by unfold downCoupling; ring

theorem downCoupling_same (z : ℂ) (t : F) : downCoupling z t t = 0 := by
  unfold downCoupling; ring

theorem downCoupling_selected (z : ℂ) :
    downCoupling z (Pi.single 0 1) (Pi.single 1 1) = z := by
  simp [downCoupling]

/-- The local source tensor is nonzero before statistics descent. -/
theorem printed_evaluation : printed (fun i =>
    colorBasis (![0,1,0,2,1,2] i) ⊗ₜ[ℂ] weakBasis (![0,0,1,1,0,1] i)) = 1 := by
  rw [printed_apply]
  norm_num [eps3, eps2, colorBasis, weakBasis, Pi.single_apply]

abbrev QF := Quark ⊗[ℂ] F
abbrev FC := MultilinearMap ℂ (fun _ : Fin 6 => QF) ℂ
private def curried (f : FC) :
    QF →ₗ[ℂ] QF →ₗ[ℂ] QF →ₗ[ℂ] QF →ₗ[ℂ] QF →ₗ[ℂ] QF →ₗ[ℂ] ℂ :=
  f.curryRight.curryRight.curryRight.curryRight.curryRight.curryRight Fin.elim0

private def firstPair (f : FC) :
    (QF ⊗[ℂ] QF) →ₗ[ℂ] QF →ₗ[ℂ] QF →ₗ[ℂ]
      QF →ₗ[ℂ] QF →ₗ[ℂ] ℂ := TensorProduct.lift (curried f)

private def secondPair (f : FC) :
    (QF ⊗[ℂ] QF) →ₗ[ℂ] (QF ⊗[ℂ] QF) →ₗ[ℂ]
      QF →ₗ[ℂ] QF →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (firstPair f p)
  map_add' p q := by ext x y z w; simp [firstPair]
  map_smul' z p := by ext x y v w; simp [firstPair]

private def lastPair (f : FC) :
    ((QF ⊗[ℂ] QF) ⊗[ℂ] (QF ⊗[ℂ] QF)) →ₗ[ℂ]
      (QF ⊗[ℂ] QF) →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (TensorProduct.lift (secondPair f) p)
  map_add' p q := by ext x y; simp
  map_smul' z p := by ext x y; simp

def orderedLift (f : FC) : SixSlotAlternation.OrderedSpace QF QF →ₗ[ℂ] ℂ :=
  TensorProduct.lift (lastPair f)

@[simp] theorem orderedLift_apply (f : FC) (a b c d e x : QF) :
    orderedLift f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] x)) =
      f ![a,b,c,d,e,x] := by
  simp only [orderedLift, lastPair, secondPair, firstPair, TensorProduct.lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, curried, MultilinearMap.curryRight_apply]
  congr 1
  ext i; fin_cases i <;> rfl


attribute [local irreducible] orderedLift

/-- Unnormalized Bose/Fermi convention: full exterior descent of the source monomial. -/
def sourceExterior : (QF × QF) [⋀^Fin 6]→ₗ[ℂ] ℂ :=
  SixSlotAlternation.alternating (orderedLift flavored)

def probe (i : Fin 6) : QF :=
  (colorBasis (![0,2,2,1,0,1] i) ⊗ₜ[ℂ] weakBasis (![0,0,1,0,1,1] i)) ⊗ₜ[ℂ]
    Pi.single (DevMohapatraSixQuark.labels i) 1

theorem sourceExterior_evaluation : sourceExterior
    (SixSlotAlternation.slots (probe 0) (probe 2) (probe 1) (probe 3) (probe 4) (probe 5)) = -2 := by
  have h := SixSlotSpeciesSum.alternating_slots_block (orderedLift flavored)
    ![probe 0,probe 2] (fun i : Fin 4 => probe (![1,3,4,5] i))
  change sourceExterior (SixSlotAlternation.slots (probe 0) (probe 2) (probe 1)
    (probe 3) (probe 4) (probe 5)) = _ at h
  rw [h]
  simp only [SixSlotSpeciesSum.blockSum]
  simp_rw [orderedLift_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hv (a b c d e x : Fin 6) : flavored ![probe a,probe b,probe c,probe d,probe e,probe x] =
      (∏ i : Fin 6, (Pi.single (DevMohapatraSixQuark.labels (![a,b,c,d,e,x] i)) (1 : ℂ) : F)
        (DevMohapatraSixQuark.labels i)) •
        printed (fun i => colorBasis (![0,2,2,1,0,1] (![a,b,c,d,e,x] i)) ⊗ₜ[ℂ]
          weakBasis (![0,0,1,0,1,1] (![a,b,c,d,e,x] i))) := by
    have he : ![probe a,probe b,probe c,probe d,probe e,probe x] =
        fun i => probe (![a,b,c,d,e,x] i) := by funext i; fin_cases i <;> rfl
    rw [he]
    exact flavored_pure _ _
  simp_rw [hv, printed_apply]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, SixSlotSpeciesSum.downParity,
    SixSlotSpeciesSum.downIndex, DevMohapatraSixQuark.labels,
    eps3, eps2, colorBasis, weakBasis, Pi.single_apply]
/-- The literal, statistics-descended source channel is invariant under the actual action. -/
theorem sourceExterior_invariant (g : DeltaBTwoModelInterface.SymmetryGroup H)
    (v : Fin 6 → QF × QF) :
    sourceExterior (fun i => (action g 0 (v i).1, action g 1 (v i).2)) = sourceExterior v := by
  have hr (w : Fin 6 → QF × QF) :
      SixSlotAlternation.ordered (orderedLift flavored)
        (fun i => (action g 0 (w i).1, action g 1 (w i).2)) =
      SixSlotAlternation.ordered (orderedLift flavored) w := by
    simp only [SixSlotAlternation.ordered, MultilinearMap.mk'_apply, orderedLift_apply]
    have he := flavored_invariant g ![(w 0).1,(w 1).2,(w 2).1,(w 3).2,(w 4).2,(w 5).2]
    convert he using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold sourceExterior SixSlotAlternation.alternating
  simp only [MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact hr (v ∘ p)

theorem sourceExterior_nonzero : sourceExterior ≠ 0 := by
  intro hz
  have he := sourceExterior_evaluation
  rw [hz] at he
  norm_num at he

/-- z is a supplied scalar coefficient, not a derived matching calculation. -/
theorem weighted_nonzero_iff (z : ℂ) : z • sourceExterior ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro h hz; exact h (by simp [hz])
  · intro hz h
    exact sourceExterior_nonzero ((smul_eq_zero.mp h).resolve_left hz)
end
end GUT.DevMohapatraConnection
