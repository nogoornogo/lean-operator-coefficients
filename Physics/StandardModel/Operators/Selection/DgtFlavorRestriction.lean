import Physics.StandardModel.Operators.Selection.ComposableBLSupport
import Physics.StandardModel.Operators.Dipole.ComposableDipoleSelection
import Math.RepresentationTheory.Weights.CyclicCharge

/-! Restricted DGT m=1,n=3 SM/Higgs and prescribed dipole controls. -/
namespace Physics.DgtFlavorRestriction
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open scoped TensorProduct
abbrev Flavor := Fin 3 → ℂ
abbrev IR := CyclicCharge.Group 9

def embedding : IR →* Circle where
  toFun g := ZMod.toCircle (Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' _ _ := by simp [AddChar.map_add_eq_mul]

theorem embedding_injective : Function.Injective embedding := by
  intro g h he
  exact congrArg Multiplicative.ofAdd (ZMod.injective_toCircle he)

def xcharge (u : Species) (i : Fin 3) : ℤ :=
  baryon u - 9 * lepton u * (if i = 1 then 1 else 0)

def diagonal (q : Fin 3 → ℤ) : Representation ℂ Circle Flavor where
  toFun z := LinearMap.pi (fun i => MixedChargeSelection.circleCharacter z (q i) • LinearMap.proj i)
  map_one' := by ext v i; simp [MixedChargeSelection.circleCharacter]
  map_mul' z w := by
    ext v i
    simp [MixedChargeSelection.circleCharacter, mul_zpow, mul_assoc]

def uvFlavor (u : Species) : Representation ℂ Circle Flavor := diagonal (xcharge u)

def cyclicCopies {V : Type*} [AddCommGroup V] [Module ℂ V] (q : ℤ) : Representation ℂ IR V where
  toFun g := LinearMap.lsmul ℂ V (MixedChargeSelection.cyclicCharacter g (q : ZMod 9))
  map_one' := by ext; simp [MixedChargeSelection.cyclicCharacter]
  map_mul' g h := by
    ext
    simp [MixedChargeSelection.cyclicCharacter, mul_add, AddChar.map_add_eq_mul,
      smul_smul, mul_comm]

def irFlavor (u : Species) : Representation ℂ IR Flavor := cyclicCopies (baryon u)
def irScalar (_u : BnvMixedInput.ScalarSpecies) : Representation ℂ IR ℂ := cyclicCopies 0

def uvScalar (_u : BnvMixedInput.ScalarSpecies) : Representation ℂ Circle ℂ :=
  Representation.trivial ℂ Circle ℂ

theorem scalar_restriction (u : BnvMixedInput.ScalarSpecies) :
    (uvScalar u).comp embedding = irScalar u := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  simp [uvScalar, irScalar, cyclicCopies, MixedChargeSelection.cyclicCharacter]

theorem phase_restriction (g : IR) (q : ℤ) :
    MixedChargeSelection.circleCharacter (embedding g) q =
      MixedChargeSelection.cyclicCharacter g (q : ZMod 9) := by
  change (ZMod.stdAddChar (Multiplicative.toAdd g)) ^ q = ZMod.stdAddChar ((q : ZMod 9) * _)
  simpa [zsmul_eq_mul] using ((ZMod.stdAddChar (N := 9)).map_zsmul_eq_zpow q
    (Multiplicative.toAdd g)).symm

theorem charge_restriction (u : Species) (i : Fin 3) :
    (xcharge u i : ZMod 9) = (baryon u : ZMod 9) := by
  have hn : (9 : ZMod 9) = 0 := by decide
  simp only [xcharge, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  rw [hn]
  simp

theorem flavor_restriction (u : Species) : (uvFlavor u).comp embedding = irFlavor u := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change MixedChargeSelection.circleCharacter (embedding g) (xcharge u i) * v i =
    MixedChargeSelection.cyclicCharacter g (baryon u : ZMod 9) * v i
  rw [phase_restriction, charge_restriction]

theorem actual_field_restriction (u : Species)
    (k : StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) (g : IR)
    (v : DeltaLOneSignedFields.Field (F := fun _ => Flavor) u) :
    DeltaLOneSignedFields.field irFlavor u (k,g) v =
      DeltaLOneSignedFields.field uvFlavor u (k,embedding g) v := by
  have hf : irFlavor u g = uvFlavor u (embedding g) :=
    (congrArg (fun r : Representation ℂ IR Flavor => r g) (flavor_restriction u)).symm
  have he : DeltaLOneSignedFields.field irFlavor u (k,g) =
      DeltaLOneSignedFields.field uvFlavor u (k,embedding g) := by
    apply TensorProduct.ext'
    intro x y
    simp only [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
      Representation.tprod_apply, TensorProduct.map_tmul]
    change DeltaLOneSignedFields.localField u k x ⊗ₜ[ℂ] irFlavor u g y =
      DeltaLOneSignedFields.localField u k x ⊗ₜ[ℂ] uvFlavor u (embedding g) y
    rw [hf]
  exact LinearMap.congr_fun he v

def blCharacter (g : IR) : AddChar (ℤ × ℤ) ℂ where
  toFun q := MixedChargeSelection.cyclicCharacter g (q.1 : ZMod 9)
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := by simp [AddChar.map_add_eq_mul]

theorem bl_detect (q : ℤ × ℤ) (h : ComposableBLSupport.bOneTwo q) :
    ∃ g : IR, blCharacter g q ≠ 1 := by
  apply (MixedChargeSelection.cyclic_detect_iff (q.1 : ZMod 9)).mpr
  intro hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd q.1 9).mp hz
  unfold ComposableBLSupport.bOneTwo at h
  omega

theorem all_bnv_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input irFlavor irScalar ComposableBLSupport.bOneTwo n m, f = 0 := by
  apply ComposableBLSupport.forbidden _ _ _ blCharacter
  · intro g u v; rfl
  · intro g u v; rfl
  · intro n m p s ht; exact bl_detect _ ht

theorem residual_bnv_forbidden (n m : ℕ)
    (q : ComposableBLSupport.Residual irFlavor irScalar ComposableBLSupport.bOneTwo n m) : q = 0 := by
  let e := ComposableBLSupport.equiv irFlavor irScalar ComposableBLSupport.bOneTwo n m
  calc
    q = e (e.symm q) := (e.apply_symm_apply q).symm
    _ = e 0 := congrArg e (all_bnv_forbidden n m (e.symm q))
    _ = 0 := e.map_zero

def leptonUV : Representation ℂ Circle Flavor := uvFlavor 3
def leptonIR : Representation ℂ IR Flavor := leptonUV.comp embedding

theorem electronUV_eq : uvFlavor 4 = leptonUV := by
  change diagonal (xcharge 4) = diagonal (xcharge 3)
  rw [show xcharge 4 = xcharge 3 by decide]

theorem electron_restriction : (uvFlavor 4).comp embedding = leptonIR := by
  rw [electronUV_eq]
  rfl

theorem leptonIR_trivial : leptonIR = Representation.trivial ℂ IR Flavor := by
  rw [leptonIR, leptonUV, flavor_restriction]
  ext g v i
  simp [irFlavor, cyclicCopies, baryon]

def mu : Flavor := Pi.single 1 1
def targetVector (i : Fin 2) : Flavor := Pi.single (if i = 0 then 0 else 2) 1
def targetCovector (i : Fin 2) : Module.Dual ℂ Flavor :=
  LinearMap.proj (if i = 0 then 0 else 2)

theorem uv_mu_weight : leptonUV (-1 : Circle) mu = (-1 : ℂ) • mu := by
  ext i; fin_cases i <;> norm_num [leptonUV, uvFlavor, diagonal, xcharge, baryon,
    lepton, mu, MixedChargeSelection.circleCharacter]

theorem uv_target_weight (i : Fin 2) (v : Flavor) :
    targetCovector i (leptonUV (-1 : Circle) v) = (1 : ℂ) * targetCovector i v := by
  fin_cases i <;> simp [targetCovector, leptonUV, uvFlavor, diagonal, xcharge, baryon,
    lepton, MixedChargeSelection.circleCharacter]

theorem uv_dipoles_forbidden :
    ComposableDipoleSelection.selector leptonUV leptonUV (fun _ : Fin 2 => mu) targetCovector = 0 := by
  apply ComposableDipoleSelection.forbidden_of_weights
  intro i
  exact ⟨-1,-1,1,uv_mu_weight,uv_target_weight i, by norm_num⟩

def bridge (i : Fin 2) : IntertwiningMap leptonIR leptonIR where
  toLinearMap := (LinearMap.proj 1).smulRight (targetVector i)
  isIntertwining' g := by rw [leptonIR_trivial]; rfl

theorem bridge_selected (i : Fin 2) : targetCovector i (bridge i mu) = 1 := by
  fin_cases i <;> simp [targetCovector, bridge, targetVector, mu]

/-- Same linear map, with equivariance restricted to the proved subgroup. -/
def restrictMap : IntertwiningMap leptonUV leptonUV →ₗ[ℂ] IntertwiningMap leptonIR leptonIR where
  toFun k := { toLinearMap := k.toLinearMap, isIntertwining' g := k.isIntertwining' (embedding g) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem uv_evaluation_zero (i : Fin 2) (k : IntertwiningMap leptonUV leptonUV) :
    targetCovector i (k mu) = 0 :=
  DipoleFlavorSelection.evaluation_zero_of_distinct_weights leptonUV leptonUV mu
    (targetCovector i) (-1) (-1) 1 uv_mu_weight (uv_target_weight i) (by norm_num) k

theorem bridge_not_restricted (i : Fin 2) : ¬ ∃ k, restrictMap k = bridge i := by
  rintro ⟨k,hk⟩
  have he := uv_evaluation_zero i k
  change targetCovector i (restrictMap k mu) = 0 at he
  rw [hk, bridge_selected] at he
  exact one_ne_zero he

theorem restriction_not_surjective : ¬ Function.Surjective restrictMap := by
  intro h
  exact bridge_not_restricted 0 (h (bridge 0))

def irWitness (i : Fin 2) : DipoleFlavorSelection.Coefficients leptonIR leptonIR :=
  (DipoleSMCoefficient.equiv leptonIR leptonIR).symm (bridge i,0)

theorem irWitness_selected (i : Fin 2) :
    DipoleFlavorSelection.selector leptonIR leptonIR mu (targetCovector i) (irWitness i) = (1,0) := by
  change (targetCovector i (((DipoleSMCoefficient.equiv _ _) (irWitness i)).1 mu),
    targetCovector i (((DipoleSMCoefficient.equiv _ _) (irWitness i)).2 mu)) = _
  rw [irWitness, LinearEquiv.apply_symm_apply]
  simp [bridge_selected]

theorem ir_dipoles_allowed (i : Fin 2) :
    ∃ c : DipoleFlavorSelection.Coefficients leptonIR leptonIR,
      DipoleFlavorSelection.selector leptonIR leptonIR mu (targetCovector i) c ≠ 0 := by
  exact ⟨irWitness i, by rw [irWitness_selected]; simp⟩

theorem condensate_fixed (g : IR) : MixedChargeSelection.circleCharacter (embedding g) 9 = 1 := by
  rw [phase_restriction]
  change MixedChargeSelection.cyclicCharacter g (9 : ZMod 9) = 1
  rw [show (9 : ZMod 9) = 0 by decide]
  exact (MixedChargeSelection.cyclicCharacter g).map_zero_eq_one

theorem fermion_conjugates (i : Fin 5) (j : Fin 3) :
    xcharge ⟨i.val+5, by omega⟩ j = -xcharge ⟨i.val, by omega⟩ j := by
  fin_cases i <;> fin_cases j <;> norm_num [xcharge, baryon, lepton]

theorem printed_dictionary : xcharge 0 = ![1,1,1] ∧ xcharge 3 = ![0,-9,0] ∧
    xcharge 4 = ![0,-9,0] := by decide
end
end Physics.DgtFlavorRestriction
