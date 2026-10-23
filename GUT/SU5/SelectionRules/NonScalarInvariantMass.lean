import GUT.SU5.SelectionRules.InvariantMassNormalForm
import GUT.SU5.SelectionRules.NonScalarCopyMass
import Mathlib.LinearAlgebra.TensorProduct.Pi

open Physics

/-! Arbitrary invariant mass on common non-scalar copies: coordinate bridges
are derived, and residual equivariance is extracted from the actual mass. -/
namespace GUT.SU5.NonScalarInvariantMass
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter StandardSMGaugeTensor SMEpsilonTensor
open BipartiteNormalForm InvariantMassNormalForm NonScalarCopyMass
open ExternalInvariantTensor ContinuousRepresentationScope CompactEmbeddingClassification
open scoped TensorProduct
universe u
local instance : AddCommGroup Ten := inferInstance
local instance : AddCommGroup Quark := inferInstance
local instance : Nontrivial Quark := Module.nontrivial_of_finrank_pos (R := ℂ)
  (by simp [Quark, Color, Weak, Module.finrank_tensorProduct])

section Coordinates
variable {G V A : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup A] [Module ℂ A] {n : ℕ}

def tensorCoordinates (b : Module.Basis (Fin n) ℂ A) : V ⊗[ℂ] A ≃ₗ[ℂ] (Fin n → V) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) b.equivFun).trans
    ((TensorProduct.piRight ℂ ℂ V (fun _ : Fin n => ℂ)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.rid ℂ V))

@[simp] theorem tensorCoordinates_tmul (b : Module.Basis (Fin n) ℂ A) (v : V) (x : A) (i : Fin n) :
    tensorCoordinates b (v ⊗ₜ[ℂ] x) i = b.repr x i • v := by
  simp [tensorCoordinates, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

def tensorCopiesEquiv (r : Representation ℂ G V) (b : Module.Basis (Fin n) ℂ A) :
    Equiv (r.tprod (Representation.trivial ℂ G A)) (FiniteSpectrum.copies n r) where
  toLinearEquiv := tensorCoordinates b
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v x
    funext i
    simp [Representation.tprod_apply]

end Coordinates

variable {H : Type*} [Group H] {S T : Type u}

section Algebraic
variable [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T) (psi : H →* Circle)

private def gaugeInclusion : GaugeGroup →* GaugeGroup × H := MonoidHom.inl _ _

def tenCoordinates (a : Representation ℂ H S) {n : ℕ} (b : Module.Basis (Fin n) ℂ S) :
    Equiv ((external (ten.comp hom) a).comp gaugeInclusion)
      (FiniteSpectrum.copies n (ten.comp hom)) where
  toLinearEquiv := tensorCoordinates b
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v x
    funext i
    change tensorCoordinates b (ten (hom g) v ⊗ₜ[ℂ] a 1 x) i =
      ten (hom g) (tensorCoordinates b (v ⊗ₜ[ℂ] x) i)
    simp

def sourceCoordinates {n : ℕ} (b : Module.Basis (Fin n) ℂ S) :
    Equiv ((sourceRho s psi).comp gaugeInclusion) (sourceSM n) where
  toLinearEquiv := LinearEquiv.prodCongr (tensorCoordinates b) (LinearEquiv.refl ℂ BarFive)
  isIntertwining' g := by
    apply LinearMap.ext
    rintro ⟨x,y⟩
    apply Prod.ext
    · exact (tenCoordinates s b).isIntertwining _ _ g x
    · change (psi 1 : ℂ) • antifundamental (hom g) y = antifundamental (hom g) y
      simp


def targetCoordinates {n : ℕ} (b : Module.Basis (Fin n) ℂ T) :
    Equiv ((targetRho t).comp gaugeInclusion) (targetSM n) := tenCoordinates t b


theorem source_no_pairings : NoPairings (sourceRho s psi) (sourceRho s psi) := by
  apply of_comp gaugeInclusion
  exact BipartiteNormalForm.equiv (sourceCoordinates s psi (Module.finBasis ℂ S))
    (sourceCoordinates s psi (Module.finBasis ℂ S)) (InvariantMassNormalForm.source_no_pairings _)

theorem target_dual_no_pairings : NoPairings (targetRho t).dual (targetRho t).dual := by
  apply of_comp gaugeInclusion
  rw [SplitRepresentationProjection.dual_comp]
  exact BipartiteNormalForm.equiv
    (SplitRepresentationProjection.dualEquiv (targetCoordinates t (Module.finBasis ℂ T)))
    (SplitRepresentationProjection.dualEquiv (targetCoordinates t (Module.finBasis ℂ T)))
    (InvariantMassNormalForm.target_dual_no_pairings _)


theorem normal_form (B : InvariantWeylMass.SymmetricMass (fieldsRho s t psi)) :
    B.form = (InvariantWeylMass.ofDirac (crossMap (sourceRho s psi) (targetRho t) B)).form :=
  BipartiteNormalForm.normal_form _ _ B (source_no_pairings s psi) (target_dual_no_pairings t)


def coordinateMap (M : IntertwiningMap (sourceRho s psi) (targetRho t)) :
    IntertwiningMap (sourceSM (Module.finrank ℂ S)) (targetSM (Module.finrank ℂ T)) :=
  (targetCoordinates t (Module.finBasis ℂ T)).toIntertwiningMap.comp
    (({ toLinearMap := M.toLinearMap
        isIntertwining' := fun g => M.isIntertwining' (g,1) } :
      IntertwiningMap ((sourceRho s psi).comp gaugeInclusion)
        ((targetRho t).comp gaugeInclusion)).comp
      (sourceCoordinates s psi (Module.finBasis ℂ S)).symm.toIntertwiningMap)

def speciesLinear (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (k : MixedTenMass.RowWeights → ℂ) : S →ₗ[ℂ] T :=
  (Module.finBasis ℂ T).equivFun.symm.toLinearMap.comp
    ((MatrixTenMass.matrixMap (fun j i => k (rows (coordinateMap s t psi M) j i))).comp
      (Module.finBasis ℂ S).equivFun.toLinearMap)

theorem speciesLinear_coordinates (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (k : MixedTenMass.RowWeights → ℂ) (x : S) (j : Fin (Module.finrank ℂ T)) :
    (Module.finBasis ℂ T).repr (speciesLinear s t psi M k x) j =
      ∑ i, k (rows (coordinateMap s t psi M) j i) * (Module.finBasis ℂ S).repr x i := by
  change (Module.finBasis ℂ T).equivFun
    ((Module.finBasis ℂ T).equivFun.symm _) j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem coordinate_reconstruction (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (x : Source (S := S)) (j : Fin (Module.finrank ℂ T)) :
    tensorCoordinates (Module.finBasis ℂ T) (M x) j =
      ∑ i, MixedTenMass.weighted (rows (coordinateMap s t psi M) j i)
        (tensorCoordinates (Module.finBasis ℂ S) x.1 i) := by
  have he := reconstructed_map (coordinateMap s t psi M)
    (sourceCoordinates s psi (Module.finBasis ℂ S) x) j
  change (targetCoordinates t (Module.finBasis ℂ T)).toLinearEquiv
    (M ((sourceCoordinates s psi (Module.finBasis ℂ S)).toLinearEquiv.symm
      ((sourceCoordinates s psi (Module.finBasis ℂ S)).toLinearEquiv x))) j = _ at he
  rw [LinearEquiv.symm_apply_apply] at he
  exact he

theorem weighted_decompose (r : MixedTenMass.RowWeights) (v : Ten) :
    MixedTenMass.weighted r v =
      r.quark • MixedTenMass.weighted quarkWeight v +
      r.up • MixedTenMass.weighted upWeight v +
      r.electron • MixedTenMass.weighted electronWeight v := by
  let E := ExteriorSquareBranching.tenEquiv.toLinearEquiv
  apply E.injective
  simp only [map_add, map_smul]
  rw [MixedTenMass.weighted_apply, MixedTenMass.weighted_apply,
    MixedTenMass.weighted_apply, MixedTenMass.weighted_apply]
  change E (E.symm _) = r.quark • E (E.symm _) + r.up • E (E.symm _) + r.electron • E (E.symm _)
  simp [quarkWeight, upWeight, electronWeight]


def reconstructedLinear (M : IntertwiningMap (sourceRho s psi) (targetRho t)) :
    Source (S := S) →ₗ[ℂ] Target (T := T) :=
  (TensorProduct.map (MixedTenMass.weighted quarkWeight).toLinearMap
      (speciesLinear s t psi M MixedTenMass.RowWeights.quark) +
    TensorProduct.map (MixedTenMass.weighted upWeight).toLinearMap
      (speciesLinear s t psi M MixedTenMass.RowWeights.up) +
    TensorProduct.map (MixedTenMass.weighted electronWeight).toLinearMap
      (speciesLinear s t psi M MixedTenMass.RowWeights.electron)).comp (LinearMap.fst ℂ _ _)

theorem reconstructedLinear_eq (M : IntertwiningMap (sourceRho s psi) (targetRho t)) :
    reconstructedLinear s t psi M = M.toLinearMap := by
  apply LinearMap.ext
  rintro ⟨x,y⟩
  apply (tensorCoordinates (Module.finBasis ℂ T)).injective
  funext j
  change _ = tensorCoordinates (Module.finBasis ℂ T) (M (x,y)) j
  rw [coordinate_reconstruction]
  change tensorCoordinates (Module.finBasis ℂ T)
    (reconstructedLinear s t psi M (x,0)) j =
    ∑ i, MixedTenMass.weighted (rows (coordinateMap s t psi M) j i)
      (tensorCoordinates (Module.finBasis ℂ S) x i)
  induction x using TensorProduct.inductionOn with
  | tmul v a =>
    change tensorCoordinates (Module.finBasis ℂ T)
      ((MixedTenMass.weighted quarkWeight v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.quark a) +
       (MixedTenMass.weighted upWeight v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.up a) +
       (MixedTenMass.weighted electronWeight v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.electron a)) j = _
    simp only [map_add, Pi.add_apply, tensorCoordinates_tmul, speciesLinear_coordinates,
      Finset.sum_smul, mul_smul]
    conv_rhs =>
      arg 2
      intro i
      rw [map_smul, weighted_decompose]
      simp only [smul_add, smul_smul]
    simp only [Finset.sum_add_distrib]
    simp only [smul_smul, mul_comm]
  | add x z hx hz =>
    have hd : (x+z, (0 : BarFive)) = (x,0) + (z,0) := by simp
    rw [hd, map_add, map_add, Pi.add_apply]
    simpa only [map_add, Pi.add_apply, Finset.sum_add_distrib] using
      congrArg₂ (fun a b => a + b) hx hz


theorem quark_pure (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (v : Quark) (x : S) :
    M (MixedTenMass.quarkTen v ⊗ₜ[ℂ] x,0) =
      MixedTenMass.quarkTen v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.quark x := by
  change M.toLinearMap _ = _
  rw [← reconstructedLinear_eq s t psi M]
  simp [reconstructedLinear, MixedTenMass.quark_weighted, quarkWeight, upWeight, electronWeight]

theorem up_pure (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (v : Module.Dual ℂ Color) (x : S) :
    M (MixedTenMass.upTen v ⊗ₜ[ℂ] x,0) =
      MixedTenMass.upTen v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.up x := by
  change M.toLinearMap _ = _
  rw [← reconstructedLinear_eq s t psi M]
  simp [reconstructedLinear, MixedTenMass.up_weighted, quarkWeight, upWeight, electronWeight]

theorem electron_pure (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (v : Module.Dual ℂ ℂ) (x : S) :
    M (MixedTenMass.electronTen v ⊗ₜ[ℂ] x,0) =
      MixedTenMass.electronTen v ⊗ₜ[ℂ] speciesLinear s t psi M MixedTenMass.RowWeights.electron x := by
  change M.toLinearMap _ = _
  rw [← reconstructedLinear_eq s t psi M]
  simp [reconstructedLinear, MixedTenMass.electron_weighted, quarkWeight, upWeight, electronWeight]

section Cancellation
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem tmul_injective {v : V} (hv : v ≠ 0) :
    Function.Injective (fun x : W => v ⊗ₜ[ℂ] x) := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  intro x y he
  have hh := congrArg (fun z => TensorProduct.lid ℂ W (TensorProduct.map f LinearMap.id z)) he
  simpa [hf] using hh

end Cancellation

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem species_equivariant (M : IntertwiningMap (sourceRho s psi) (targetRho t))
    (L : S →ₗ[ℂ] T) {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (f : V →ₗ[ℂ] Ten) (hf : Function.Injective f)
    (hp : ∀ v x, M (f v ⊗ₜ[ℂ] x,0) = f v ⊗ₜ[ℂ] L x) :
    ∀ h, L.comp (s h) = (t h).comp L := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hfv : f v ≠ 0 := by intro he; apply hv; apply hf; simpa using he
  intro h
  apply LinearMap.ext
  intro x
  apply tmul_injective hfv
  change f v ⊗ₜ[ℂ] L (s h x) = f v ⊗ₜ[ℂ] t h (L x)
  have hm := M.isIntertwining _ _ (1,h) (f v ⊗ₜ[ℂ] x,0)
  have hin : sourceRho s psi (1,h) (f v ⊗ₜ[ℂ] x,0) = (f v ⊗ₜ[ℂ] s h x,0) := by
    apply Prod.ext
    · change ten (hom 1) (f v) ⊗ₜ[ℂ] s h x = _
      simp
    · change barAction psi (1,h) 0 = 0
      exact map_zero _
  rw [hin, hp, hp] at hm
  change f v ⊗ₜ[ℂ] L (s h x) = ten (hom 1) (f v) ⊗ₜ[ℂ] t h (L x) at hm
  simpa using hm


def quarkMap (M : IntertwiningMap (sourceRho s psi) (targetRho t)) : IntertwiningMap s t where
  toLinearMap := speciesLinear s t psi M MixedTenMass.RowWeights.quark
  isIntertwining' := species_equivariant s t psi M _ MixedTenMass.quarkTen
    MixedTenMass.quarkTen_injective (quark_pure s t psi M)

def upMap (M : IntertwiningMap (sourceRho s psi) (targetRho t)) : IntertwiningMap s t where
  toLinearMap := speciesLinear s t psi M MixedTenMass.RowWeights.up
  isIntertwining' := species_equivariant s t psi M _ MixedTenMass.upTen
    MixedTenMass.upTen_injective (up_pure s t psi M)

def electronMap (M : IntertwiningMap (sourceRho s psi) (targetRho t)) : IntertwiningMap s t where
  toLinearMap := speciesLinear s t psi M MixedTenMass.RowWeights.electron
  isIntertwining' := species_equivariant s t psi M _ MixedTenMass.electronTen
    MixedTenMass.electronTen_injective (electron_pure s t psi M)


theorem massMap_eq (M : IntertwiningMap (sourceRho s psi) (targetRho t)) :
    NonScalarCopyMass.massMap s t psi (quarkMap s t psi M) (upMap s t psi M)
      (electronMap s t psi M) = M := by
  apply IntertwiningMap.ext
  exact reconstructedLinear_eq s t psi M


theorem species_normal_form (B : InvariantWeylMass.SymmetricMass (fieldsRho s t psi)) :
    ∃ Mq Mu Me : IntertwiningMap s t,
      B.form = (NonScalarCopyMass.mass s t psi Mq Mu Me).form := by
  let M := crossMap (sourceRho s psi) (targetRho t) B
  refine ⟨quarkMap s t psi M, upMap s t psi M, electronMap s t psi M, ?_⟩
  rw [normal_form s t psi B]
  change (InvariantWeylMass.ofDirac M).form = (InvariantWeylMass.ofDirac
    (NonScalarCopyMass.massMap s t psi (quarkMap s t psi M) (upMap s t psi M)
      (electronMap s t psi M))).form
  rw [massMap_eq]


local instance (Mq : IntertwiningMap s t) : AddCommGroup (QuarkSpace s t Mq psi) := inferInstance
local instance (Mu : IntertwiningMap s t) : AddCommGroup (UpSpace s t Mu psi) := inferInstance
local instance (Me : IntertwiningMap s t) : AddCommGroup (ElectronSpace s t Me psi) := inferInstance

/-- Arbitrary original mass and original target metric, with no supplied
target unitarity. Source semisimplicity replaces topology and compactness. -/
theorem arbitrary_mass_light_exterior_of_semisimple
    (hss : IsSemisimpleRepresentation s)
    (B : InvariantWeylMass.SymmetricMass (fieldsRho s t psi))
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ Mq Mu Me : IntertwiningMap s t,
      B.form = (NonScalarCopyMass.mass s t psi Mq Mu Me).form ∧
      (∀ x : QuarkSpace s t Mq psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : UpSpace s t Mu psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : ElectronSpace s t Me psi, x.val ∈ B.radical.toSubmodule) ∧
      PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
        (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨Mq,Mu,Me,he⟩ := species_normal_form s t psi B
  obtain ⟨hq,hup,hel,hf⟩ := exists_light_exterior_of_semisimple s t Mq Mu Me psi hss hd
  have hm (x : Fields (S := S) (T := T)) :
      x ∈ B.radical.toSubmodule ↔ x ∈ (NonScalarCopyMass.mass s t psi Mq Mu Me).radical.toSubmodule := by
    rw [InvariantWeylMass.SymmetricMass.mem_radical,
      InvariantWeylMass.SymmetricMass.mem_radical, he]
  exact ⟨Mq,Mu,Me,he,fun x => (hm x.val).mpr (hq x),
    fun x => (hm x.val).mpr (hup x),fun x => (hm x.val).mpr (hel x),hf⟩


end Algebraic

section Analytic
variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T) (psi : H →* Circle)
local instance (Mq : IntertwiningMap s t) : AddCommGroup (QuarkSpace s t Mq psi) := inferInstance
local instance (Mu : IntertwiningMap s t) : AddCommGroup (UpSpace s t Mu psi) := inferInstance
local instance (Me : IntertwiningMap s t) : AddCommGroup (ElectronSpace s t Me psi) := inferInstance

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) (hu : IsUnitaryRepresentation t)

include hs ht hu in
/-- No species mass presentation is assumed: it is extracted from arbitrary B,
and the actual participating fields are light for that same B. -/
theorem arbitrary_mass_light_exterior
    (B : InvariantWeylMass.SymmetricMass (fieldsRho s t psi))
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ Mq Mu Me : IntertwiningMap s t,
      B.form = (NonScalarCopyMass.mass s t psi Mq Mu Me).form ∧
      (∀ x : QuarkSpace s t Mq psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : UpSpace s t Mu psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : ElectronSpace s t Me psi, x.val ∈ B.radical.toSubmodule) ∧
      PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
        (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨Mq,Mu,Me,he⟩ := species_normal_form s t psi B
  obtain ⟨hq,hup,hel,hf⟩ := exists_light_exterior s t Mq Mu Me psi hs ht hu hd
  have hm (x : Fields (S := S) (T := T)) :
      x ∈ B.radical.toSubmodule ↔ x ∈ (NonScalarCopyMass.mass s t psi Mq Mu Me).radical.toSubmodule := by
    rw [InvariantWeylMass.SymmetricMass.mem_radical,
      InvariantWeylMass.SymmetricMass.mem_radical, he]
  exact ⟨Mq,Mu,Me,he,fun x => (hm x.val).mpr (hq x),
    fun x => (hm x.val).mpr (hup x),fun x => (hm x.val).mpr (hel x),hf⟩


include hs ht in
/-- Arbitrary original mass and original target metric, with no supplied
target unitarity. Unitarization is internal to the common-kernel proof. -/
theorem arbitrary_mass_light_exterior_of_continuous
    (B : InvariantWeylMass.SymmetricMass (fieldsRho s t psi))
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    ∃ Mq Mu Me : IntertwiningMap s t,
      B.form = (NonScalarCopyMass.mass s t psi Mq Mu Me).form ∧
      (∀ x : QuarkSpace s t Mq psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : UpSpace s t Mu psi, x.val ∈ B.radical.toSubmodule) ∧
      (∀ x : ElectronSpace s t Me psi, x.val ∈ B.radical.toSubmodule) ∧
      PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
        (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨Mq,Mu,Me,he⟩ := species_normal_form s t psi B
  obtain ⟨hq,hup,hel,hf⟩ := exists_light_exterior_of_continuous s t Mq Mu Me psi hs ht hd
  have hm (x : Fields (S := S) (T := T)) :
      x ∈ B.radical.toSubmodule ↔ x ∈ (NonScalarCopyMass.mass s t psi Mq Mu Me).radical.toSubmodule := by
    rw [InvariantWeylMass.SymmetricMass.mem_radical,
      InvariantWeylMass.SymmetricMass.mem_radical, he]
  exact ⟨Mq,Mu,Me,he,fun x => (hm x.val).mpr (hq x),
    fun x => (hm x.val).mpr (hup x),fun x => (hm x.val).mpr (hel x),hf⟩

end Analytic

end
end GUT.SU5.NonScalarInvariantMass
