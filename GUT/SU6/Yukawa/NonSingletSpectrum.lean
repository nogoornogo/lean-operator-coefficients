import GUT.SU6.Yukawa.NonSingletCoordinates
import Math.RepresentationTheory.Decomposition.TwoCopyKernel
import Physics.StandardModel.Gauge.Tensors.TwistedFundamentalIrreducibility
import GUT.SU6.Yukawa.ResidualConstituents

open Physics

open Math

/-! Exact residual representations of the five-parameter actual mass family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6NonSingletSpectrum
noncomputable section
open StandardSMUVFields StandardSMGaugeTensor SU6NonSingletCoordinates
open SU6YukawaLight SU6FiveCouplings SU6YukawaSinglets SplitRepresentationProjection

theorem five_smul_zero (a : ℂ) (x : UV) :
    a • (coords x).2.1.1 = 0 ↔ ∀ i : Fin 5, a * zcoord x i.castSucc = 0 := by
  rw [← fiveEquiv.map_eq_zero_iff, map_smul]
  simp only [funext_iff, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, coords_five_value]

theorem dual_mix_zero (a b : ℂ) (x : UV) :
    a • (coords x).2.1.2.1 + b • (coords x).2.1.2.2 = 0 ↔
      ∀ i : Fin 5, a * fcoord x i.castSucc + b * gcoord x i.castSucc = 0 := by
  rw [dual_zero_iff]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    (coords_dual_probe x _).1, (coords_dual_probe x _).2]

variable (H : Type*) [CommGroup H]

abbrev ten : Representation ℂ (GaugeGroup × H) Ten := tenRho.comp (MonoidHom.fst GaugeGroup H)
abbrev five : Representation ℂ (GaugeGroup × H) Five := fiveRho.comp (MonoidHom.fst GaugeGroup H)
abbrev dualFive : Representation ℂ (GaugeGroup × H) DualFive :=
  fiveRho.dual.comp (MonoidHom.fst GaugeGroup H)
abbrev mixing (a b : ℂ) := TwoCopyKernel.sector (five H) (dualFive H) a b
abbrev singlet (u v w : ℂ) := Representation.trivial ℂ (GaugeGroup × H) (Kernel u v w)

theorem radical_coordinates (a b u v w : ℂ) (x : UV) :
    x ∈ (mass H a b u v w).radical.toSubmodule ↔
      (coords x).2.1 ∈ (mixing H a b).toSubmodule ∧ (coords x).2.2 ∈ Kernel u v w := by
  rw [radical_iff]
  change LightConditions a b u v w x ↔
    (a • (coords x).2.1.1 = 0 ∧ b • (coords x).2.1.1 = 0 ∧
      a • (coords x).2.1.2.1 + b • (coords x).2.1.2.2 = 0) ∧ _
  rw [five_smul_zero, five_smul_zero, dual_mix_zero, coords_singlet, singlet_kernel_iff]
  simp only [LightConditions, forall_and, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  tauto

def model (a b u v w : ℂ) :=
  (ten H).prod ((mixing H a b).toRepresentation.prod (singlet H u v w))

def radicalEquiv (a b u v w : ℂ) :
    Representation.Equiv (mass H a b u v w).radical.toRepresentation (model H a b u v w) where
  toLinearEquiv := {
    toFun x := ((coords x.val).1,
      (⟨(coords x.val).2.1, ((radical_coordinates H a b u v w x.val).mp x.property).1⟩,
       ⟨(coords x.val).2.2, ((radical_coordinates H a b u v w x.val).mp x.property).2⟩))
    invFun y := ⟨coords.symm (y.1, (y.2.1.val, y.2.2.val)), by
      rw [radical_coordinates, LinearEquiv.apply_symm_apply]
      exact ⟨y.2.1.property, y.2.2.property⟩⟩
    left_inv x := Subtype.ext (coords.symm_apply_apply x.val)
    right_inv y := by simp only [LinearEquiv.apply_symm_apply]
    map_add' x y := by simp only [Submodule.coe_add, map_add]; rfl
    map_smul' c x := by simp only [Submodule.coe_smul, map_smul]; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have he := coords_action H g x.val
    apply Prod.ext
    · exact congrArg (fun z : Normal => z.1) he
    apply Prod.ext
    · apply Subtype.ext; exact congrArg (fun z : Normal => z.2.1) he
    · apply Subtype.ext
      change (coords (StandardSMUVMass.rho H g x.val)).2.2 = _
      simpa [normalRho, model, singlet] using congrArg (fun z : Normal => z.2.2) he

def nonzeroEquiv (a b u v w : ℂ) (h : a ≠ 0 ∨ b ≠ 0) :
    Representation.Equiv (mass H a b u v w).radical.toRepresentation
      ((ten H).prod ((dualFive H).prod (singlet H u v w))) :=
  (radicalEquiv H a b u v w).trans
    (prodEquiv (.refl _) (prodEquiv (TwoCopyKernel.ofNonzero (five H) (dualFive H) a b h)
      (.refl _)))

def zeroEquiv (u v w : ℂ) :
    Representation.Equiv (mass H 0 0 u v w).radical.toRepresentation
      ((ten H).prod (((five H).prod ((dualFive H).prod (dualFive H))).prod (singlet H u v w))) :=
  (radicalEquiv H 0 0 u v w).trans
    (prodEquiv (.refl _) (prodEquiv (TwoCopyKernel.ofZero (five H) (dualFive H)) (.refl _)))

abbrev splitDual := Representation.prod ((twist color (-2)).dual.comp (MonoidHom.fst GaugeGroup H))
  ((twist weak 3).dual.comp (MonoidHom.fst GaugeGroup H))
abbrev singletCopies (u v w : ℂ) := Representation.trivial ℂ (GaugeGroup × H)
  (Fin (Module.finrank ℂ (Kernel u v w)) → ℂ)

def nonzeroDecomposition (a b u v w : ℂ) (h : a ≠ 0 ∨ b ≠ 0) :
    Representation.Equiv (mass H a b u v w).radical.toRepresentation
      ((ten H).prod ((splitDual H).prod (singletCopies H u v w))) :=
  (nonzeroEquiv H a b u v w h).trans
    (prodEquiv (.refl _) (prodEquiv (SU6ResidualConstituents.residualDualFiveSplit H)
      (trivialCopiesEquiv H u v w)))

def zeroDecomposition (u v w : ℂ) :
    Representation.Equiv (mass H 0 0 u v w).radical.toRepresentation
      ((ten H).prod (((five H).prod ((splitDual H).prod (splitDual H))).prod
        (singletCopies H u v w))) :=
  (zeroEquiv H u v w).trans
    (prodEquiv (.refl _) (prodEquiv (prodEquiv (.refl _)
      (prodEquiv (SU6ResidualConstituents.residualDualFiveSplit H)
        (SU6ResidualConstituents.residualDualFiveSplit H))) (trivialCopiesEquiv H u v w)))

theorem all_yukawa_decompositions
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    ∃ c : Fin 5 → ℂ,
      generatedMass H Y = mass H (c 0) (c 1) (c 2) (c 3) (c 4) ∧
      (c 0 ≠ 0 ∨ c 1 ≠ 0 → Nonempty (Representation.Equiv
        (generatedMass H Y).radical.toRepresentation
        ((ten H).prod ((splitDual H).prod (singletCopies H (c 2) (c 3) (c 4)))))) ∧
      (c 0 = 0 ∧ c 1 = 0 → Nonempty (Representation.Equiv
        (generatedMass H Y).radical.toRepresentation
        ((ten H).prod (((five H).prod ((splitDual H).prod (splitDual H))).prod
          (singletCopies H (c 2) (c 3) (c 4)))))) := by
  obtain ⟨c, hc, _⟩ := all_yukawas H Y
  refine ⟨c, hc, ?_, ?_⟩
  · intro h
    rw [hc]
    exact ⟨nonzeroDecomposition H _ _ _ _ _ h⟩
  · rintro ⟨h0, h1⟩
    rw [hc, h0, h1]
    exact ⟨zeroDecomposition H _ _ _⟩

end
end GUT.SU6NonSingletSpectrum
