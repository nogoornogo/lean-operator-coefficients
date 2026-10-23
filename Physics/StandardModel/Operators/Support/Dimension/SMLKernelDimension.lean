import Physics.StandardModel.Operators.Support.Lepton.SMLContinuousCharacter
import Physics.StandardModel.Operators.Support.Coordinates.SMConstantContentRanks

/-! Actual local L/Higgs kernel dimensions from the uniform weight formula. -/
namespace Physics.SMLKernelDimension
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights
open scoped TensorProduct
variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev pattern := SMLCompactWeyl.pattern

theorem source_color_fixed (n : ℕ) (c : ColorPlaneCircles.SU3)
    (x : PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (pattern n)) :
    SMIntegralLocalWeights.source flavor (pattern n) (color c) x = x := by
  have hf : DeltaLOneSignedFields.field flavor 3 ((color c),1) = LinearMap.id := by
    apply TensorProduct.ext'
    intro a v
    induction a using TensorProduct.inductionOn with
    | tmul a b =>
      simp [DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField,
        ExternalInvariantTensor.external, Representation.tprod_apply,
        StandardSMGaugeTensor.lepton, StandardSMGaugeTensor.twist,
        StandardSMGaugeTensor.phase, StandardSMGaugeTensor.weak, color]
    | add a b ha hb => simp_all only [TensorProduct.add_tmul, map_add, LinearMap.id_apply]
  have he : PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) (pattern n)
      ((color c),1) = (1 : ℂ) • LinearMap.id := by
    apply PiTensorProduct.ext
    ext v
    simp only [PatternExteriorSource.Raw, MultilinearInvariantHom.tensorRepresentation_tprod,
      pattern, hf, LinearMap.id_apply, one_smul, LinearMap.compMultilinearMap_apply]
  exact (PatternExteriorSource.source_scalar _ _ ((color c),1) 1 he x).trans (one_smul ℂ x)

theorem boson_color_fixed (m : ℕ) (delta : ℤ) (c : ColorPlaneCircles.SU3)
    (x : Sym[ℂ]^m WeakDoubletScalars.Doublet) : boson (H := H) m delta (color c) x = x := by
  have hh : SMHiggsConstituents.character (H := H) (color c,1) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, StandardSMGaugeTensor.phase, color]
  change ((SMHiggsConstituents.character ^ delta) (color c,1) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 x = x
  rw [MonoidHom.zpow_apply, hh, one_zpow, one_smul, map_one]
  rfl

theorem action_color_fixed (n m : ℕ) (delta : ℤ) (c : ColorPlaneCircles.SU3)
    (x : SMFullLocalKernel.Carrier flavor (pattern n) m) :
    SMIntegralLocalWeights.action flavor (pattern n) m delta (color c) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    change source flavor (pattern n) (color c) x ⊗ₜ[ℂ] boson m delta (color c) y = _
    rw [source_color_fixed, boson_color_fixed]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem action_hyper_fixed (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ))
    (z : Circle) (x : SMFullLocalKernel.Carrier flavor (pattern n) m) :
    SMIntegralLocalWeights.action flavor (pattern n) m delta (hyper z) x = x := by
  have hq : SMContentWeakBound.hypercharge (pattern n) + 3*delta = 0 := by
    simp [SMContentWeakBound.hypercharge, pattern, SMLCompactWeyl.pattern,
      DeltaLOneSignedInput.hypercharge, hn]
    ring
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    change source flavor (pattern n) (hyper z) x ⊗ₜ[ℂ] boson m delta (hyper z) y = _
    calc
      _ = ((z : ℂ)^SMContentWeakBound.hypercharge (pattern n) • x) ⊗ₜ[ℂ]
          ((z : ℂ)^(3*delta) • y) := congrArg₂ (fun a b => a ⊗ₜ[ℂ] b)
            (SMContentWeakBound.source_hypercharge flavor (pattern n) z x)
            (SMFiniteHiggsSupport.constituent_hypercharge m delta z y)
      _ = _ := by simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
        ← zpow_add₀ z.coe_ne_zero, add_comm (3*delta), hq, zpow_zero, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem full_fixed_of_pair (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ))
    (f : SMFullLocalKernel.Carrier flavor (pattern n) m →ₗ[ℂ] ℂ)
    (hp : ∀ k x, f (SMLWeightExpansion.action flavor n m delta k x) = f x) :
    ∀ g x, f (SMIntegralLocalWeights.action flavor (pattern n) m delta g x) = f x := by
  have hw : ∀ u x, f (SMIntegralLocalWeights.action flavor (pattern n) m delta (weak u) x) = f x := by
    intro u x
    exact hp (u,1) x
  have hs : ∀ s x, f (SMIntegralLocalWeights.action flavor (pattern n) m delta (spin s) x) = f x :=
    (SMLCompactWeyl.higgs_coefficient_fixed_iff flavor n m delta f).mpr (fun u x => hp (1,u) x)
  intro g x
  have he : g = color g.1.1 * weak g.1.2.1 * hyper g.1.2.2 * spin g.2 := by
    rcases g with ⟨⟨c,w,z⟩,s⟩
    simp [color,weak,hyper,spin,MonoidHom.inr_apply]
  rw [he]
  simp only [map_mul,Module.End.mul_apply]
  rw [action_color_fixed]
  exact (hw _ _).trans ((congrArg f (action_hyper_fixed flavor n m delta hn _ _)).trans (hs _ _))

def coefficientEquiv (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ)) :
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor (pattern n) m delta)
      ≃ₗ[ℂ] InvariantCoefficientTransport.Invariants (SMLWeightExpansion.action flavor n m delta) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' k := by
        apply LinearMap.ext
        intro x
        exact f.isIntertwining _ _ ((1,(k.1,1)), SL2SymmetricEmbeddings.compactInclusion k.2) x }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact full_fixed_of_pair flavor n m delta hn f.toLinearMap
          (fun k y => f.isIntertwining _ _ k y) g x }
  left_inv f := by apply IntertwiningMap.ext; rfl
  right_inv f := by apply IntertwiningMap.ext; rfl
  map_add' f g := by apply IntertwiningMap.ext; rfl
  map_smul' c f := by apply IntertwiningMap.ext; rfl

/-- The entire actual finite kernel has the structural L weight multiplicity. -/
theorem kernel_dimension (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ)) :
    (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern n) m delta) : ℂ) =
      SMLContinuousCharacter.weights n m (0,0) - SMLContinuousCharacter.weights n m (0,2) -
        SMLContinuousCharacter.weights n m (2,0) + SMLContinuousCharacter.weights n m (2,2) := by
  have e := (SMFullLocalKernel.coefficientEquiv flavor (pattern n) m delta).symm.trans
    (coefficientEquiv flavor n m delta hn)
  exact (congrArg (fun d : ℕ => (d : ℂ)) e.finrank_eq).trans
    (SMLContinuousCharacter.coefficient_dimension flavor n m delta)

abbrev multiplicity (n m : ℕ) : ℂ := SMLContinuousCharacter.weights n m (0,0) -
  SMLContinuousCharacter.weights n m (0,2) - SMLContinuousCharacter.weights n m (2,0) +
    SMLContinuousCharacter.weights n m (2,2)

theorem rank_add_multiplicity (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ)) :
    (Module.finrank ℂ (LinearMap.range
      (SMFullLocalKernel.constraints flavor (pattern n) m delta)) : ℂ) + multiplicity n m =
      (SMConstantContentRanks.columns 3 n m : ℂ) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (SMFullLocalKernel.constraints flavor (pattern n) m delta)
  have hd : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (pattern n) m)) → ℂ) =
      SMConstantContentRanks.columns 3 n m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact SMConstantContentRanks.carrier_dimension flavor 3 n m
  have hk : (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern n) m delta) : ℂ) =
      multiplicity n m := kernel_dimension flavor n m delta hn
  calc
    _ = (Module.finrank ℂ (LinearMap.range
        (SMFullLocalKernel.constraints flavor (pattern n) m delta)) : ℂ) +
          (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern n) m delta) : ℂ) :=
      congrArg (fun z : ℂ => _ + z) hk.symm
    _ = _ := by exact_mod_cast h.trans hd

theorem allowed_neutral_iff (n m : ℕ) (delta : ℤ) (hn : delta = (n : ℤ)) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern n) m delta)) ↔ multiplicity n m ≠ 0 := by
  rw [SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor (pattern n) m delta)]
  change SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor (pattern n) m delta) ↔
    multiplicity n m ≠ 0
  have hk : (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (pattern n) m delta) : ℂ) =
      multiplicity n m := kernel_dimension flavor n m delta hn
  exact SU2CoefficientExtraction.allowed_iff_finrank_ne_zero.trans
    (congrArg (fun z : ℂ => z ≠ 0) hk).to_iff

/-- Complete local support criterion for constant L contents, for all degrees
and hypercharge indices. Residual selection remains a separate condition. -/
theorem allowed_iff (n m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern n) m delta)) ↔
        delta = (n : ℤ) ∧ multiplicity n m ≠ 0 := by
  constructor
  · intro ha
    have hq := SMChargedKernelRank.local_charge flavor (pattern n) m delta ha
    have hn : delta = (n : ℤ) := by
      simp [SMContentWeakBound.hypercharge, pattern, SMLCompactWeyl.pattern,
        DeltaLOneSignedInput.hypercharge] at hq
      omega
    exact ⟨hn, (allowed_neutral_iff flavor n m delta hn).mp ha⟩
  · rintro ⟨hn,hp⟩
    exact (allowed_neutral_iff flavor n m delta hn).mpr hp

/-- Regression against the independent LLHH coefficient basis. -/
theorem multiplicity_llhh : multiplicity 2 2 = 6 := by
  have h := kernel_dimension LLHHKernelRank.flavor 2 2 2 rfl
  have he : (Module.finrank ℂ (SMFullLocalKernel.Kernel LLHHKernelRank.flavor
      LLHHKernelRank.pattern 2 2) : ℂ) = multiplicity 2 2 := h
  exact he.symm.trans (congrArg (fun n : ℕ => (n : ℂ)) LLHHKernelRank.kernel_dimension)

/-- The structural formula agrees with the independent central parity test. -/
theorem multiplicity_odd (n m : ℕ) (hn : n % 2 ≠ 0) : multiplicity n m = 0 := by
  by_contra hp
  have ha := (allowed_iff LLHHKernelRank.flavor n m (n : ℤ)).mpr ⟨rfl,hp⟩
  exact ((SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMParityKernelRank.forbidden LLHHKernelRank.flavor (pattern n) m (n : ℤ) hn)) ha

/-- Exterior capacity is retained by the structural formula. -/
theorem multiplicity_above_capacity (n m : ℕ) (hn : 12 < n) : multiplicity n m = 0 := by
  by_contra hp
  have ha := (allowed_iff LLHHKernelRank.flavor n m (n : ℤ)).mpr ⟨rfl,hp⟩
  have hlt := (SMFullLocalKernel.allowed_iff_rank_lt LLHHKernelRank.flavor (pattern n) m (n : ℤ)).mp ha
  have hd : Module.finrank ℂ (SMFullLocalKernel.Carrier LLHHKernelRank.flavor (pattern n) m) = 0 := by
    have h := SMConstantContentRanks.carrier_dimension LLHHKernelRank.flavor 3 n m
    exact h.trans (by simp [SMConstantContentRanks.columns, SMConstantContentRanks.dimension,
      Nat.choose_eq_zero_of_lt hn])
  simp only [Fintype.card_fin, hd] at hlt
  exact Nat.not_lt_zero _ hlt

end
end Physics.SMLKernelDimension
