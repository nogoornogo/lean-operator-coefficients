import Physics.StandardModel.Operators.SixQuarkFullSeed
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.RepresentationTheory.SymmetricCoefficientDressing

namespace GUT.WeinbergFullSeed
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput SMEpsilonTensor
open scoped TensorProduct BigOperators
variable {k : ℕ} [NeZero k] (q l : ZMod k)
abbrev Fermions := SixQuarkFullSeed.Fields
abbrev Bosons := NeutralHiggsPowers.Fields
abbrev LocalLepton := WeinbergModelSector.Lepton ℂ

def leptonStrip : ((Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] (Fin 3 → ℂ)) →ₗ[ℂ] LocalLepton :=
  TensorProduct.map LinearMap.id (LinearMap.proj 0)
def leptonProjection : Fermions →ₗ[ℂ] LocalLepton := leptonStrip.comp (LinearMap.proj (3 : Species))
def higgsProjection : Bosons →ₗ[ℂ] Weak :=
  (LinearMap.fst ℂ Weak (Module.Dual ℂ Weak)).comp
    (NeutralHiggsPowers.coordinates (H := CyclicCharge.Group k)).toLinearMap
def leptonInclusion : LocalLepton →ₗ[ℂ] Fermions :=
  (LinearMap.single ℂ _ 3).comp
    (TensorProduct.map LinearMap.id (LinearMap.pi (fun _ : Fin 3 => LinearMap.id)))
def higgsInclusion : Weak →ₗ[ℂ] Bosons :=
  (NeutralHiggsPowers.coordinates (H := CyclicCharge.Group k)).symm.toLinearMap.comp
    (LinearMap.inl ℂ Weak (Module.Dual ℂ Weak))

theorem lepton_right_inverse (v : LocalLepton) : leptonProjection (leptonInclusion v)=v := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp [leptonProjection,leptonInclusion,leptonStrip]
  | add a b ha hb => simp [ha,hb]
omit [NeZero k] in
theorem higgs_right_inverse (v : Weak) : higgsProjection (k := k) (higgsInclusion (k := k) v)=v := by
  simp [higgsProjection,higgsInclusion]

def localSeed : WeinbergSMInterface.ModelSector (trivial ℂ Unit ℂ) :=
  WeinbergSMInterface.oneGenerationEquiv.symm 1

theorem localSeed_nonzero : localSeed ≠ 0 := by
  intro hz
  have hh := congrArg WeinbergSMInterface.oneGenerationEquiv hz
  simp [localSeed] at hh

theorem lepton_action (g : WeinbergSMInterface.PhysicalGroup (CyclicCharge.Group k)) (v : Fermions) :
    leptonProjection (DeltaLOneSignedFields.fullRepresentation (ContentHiggsSupport.flavor q l) g v) =
      MixedChargeSelection.cyclicCharacter g.2 l •
        WeinbergSMInterface.lepton (trivial ℂ Unit ℂ) (g.1,()) (leptonProjection v) := by
  change leptonStrip (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l) 3 g (v 3)) =
    MixedChargeSelection.cyclicCharacter g.2 l • WeinbergSMInterface.lepton (trivial ℂ Unit ℂ) (g.1,()) (leptonStrip (v 3))
  generalize v 3 = x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb,smul_add]
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb,smul_add]
    | tmul w s =>
      simp [leptonStrip,DeltaLOneSignedFields.field,DeltaLOneSignedFields.localField,
        DeltaLOneSignedFields.gauge,DeltaLOneSignedFields.rightHanded,ExternalInvariantTensor.external,
        Representation.tprod_apply,ContentHiggsSupport.flavor,DuqlHiggsContent.fermionFlavor,
        DressedDuqlFamily.flavor,FlavoredCyclicSelection.flavor,FlavoredCyclicSelection.signedCharge,
        FlavoredCyclicSelection.slot,InverseCyclicSMCharges.universal,InverseCyclicSMCharges.physical,
        CyclicWeightCoordinates.diagonal_apply,WeinbergSMInterface.lepton,FourSameWeylCompleteness.action,
        MixedChargeSelection.cyclicCharacter,mul_comm]
      simp only [← TensorProduct.tmul_smul, smul_eq_mul, mul_comm]

omit [NeZero k] in
theorem higgs_action (g : WeinbergSMInterface.PhysicalGroup (CyclicCharge.Group k)) (v : Bosons) :
    higgsProjection (k := k) (NeutralHiggsPowers.action g v) =
      WeinbergSMInterface.higgs (R := Unit) (g.1,()) (higgsProjection (k := k) v) := by
  have he := (NeutralHiggsPowers.coordinates (H := CyclicCharge.Group k)).isIntertwining' g
  exact congrArg (fun f => (f v).1) he

theorem phase_two (hc : 2*l=0) (g : CyclicCharge.Group k) :
    MixedChargeSelection.cyclicCharacter g l ^ 2 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  simpa [nsmul_eq_mul] using congrArg (MixedChargeSelection.cyclicCharacter g) hc

def pullback (k : ℕ) : ((⋀[ℂ]^2 Fermions) ⊗[ℂ] Sym[ℂ]^2 Bosons) →ₗ[ℂ]
    ((⋀[ℂ]^2 LocalLepton) ⊗[ℂ] Sym[ℂ]^2 Weak) := TensorProduct.map (exteriorPower.map 2 leptonProjection)
  (SymmetricPower.map (ι := Fin 2) (higgsProjection (k := k)))

def raw (hc : 2*l=0) : BnvMixedInput.Coefficient (ContentHiggsSupport.flavor q l)
    (ContentHiggsSupport.scalar (k := k)) 2 2 where
  toLinearMap := localSeed.toLinearMap.comp (pullback k)
  isIntertwining' g := by
    apply MixedPowerDescent.ext 2 2
    intro v w
    change localSeed (pullback k
      (((DeltaLOneSignedFields.fullRepresentation (ContentHiggsSupport.flavor q l)).exteriorPower 2).tprod
        ((NeutralHiggsPowers.action (H := CyclicCharge.Group k)).symmetricPower 2) g
          (MixedWeightSupport.pure v w))) = localSeed (pullback k (MixedWeightSupport.pure v w))
    simp only [pullback,MixedWeightSupport.pure,Representation.tprod_apply,TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti,Representation.symmetricPower_apply_tprod,
      exteriorPower.map_apply_ιMulti,SymmetricPower.map_tprod,Function.comp_def]
    simp_rw [lepton_action,higgs_action]
    rw [(exteriorPower.ιMulti ℂ 2).map_smul_univ]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [phase_two l hc g.2,one_smul]
    have he := IntertwiningMap.isIntertwining _ _ localSeed (g.1,())
      (MixedWeightSupport.pure (leptonProjection ∘ v) ((higgsProjection (k := k)) ∘ w))
    simp only [WeinbergSMInterface.domain,MixedWeightSupport.pure,Representation.tprod_apply,
      TensorProduct.map_tmul,Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod,Representation.trivial_apply,Function.comp_def] at he
    convert he using 1

theorem raw_apply (hc : 2*l=0) (v : Fin 2 → Fermions) (w : Fin 2 → Bosons) :
    raw q l hc (MixedWeightSupport.pure v w) =
      localSeed (MixedWeightSupport.pure (leptonProjection ∘ v) ((higgsProjection (k := k)) ∘ w)) := by
  simp [raw,pullback,MixedWeightSupport.pure,exteriorPower.map_apply_ιMulti,SymmetricPower.map_tprod,Function.comp_def]

theorem raw_nonzero (hc : 2*l=0) : raw q l hc ≠ 0 := by
  intro hz
  apply localSeed_nonzero
  apply MixedWeightSupport.ext
  intro v w
  change localSeed (MixedWeightSupport.pure v w)=0
  have he := congrArg (fun f => f (MixedWeightSupport.pure (leptonInclusion ∘ v) ((higgsInclusion (k := k)) ∘ w))) hz
  simpa [raw_apply,Function.comp_def,lepton_right_inverse,higgs_right_inverse] using he

theorem supported (hc : 2*l=0) : raw q l hc ∈
    ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 2 0 := by
  intro p s hs v w
  by_contra hn
  have hp : ContentHiggsSupport.leptonPair p := by
    intro i
    by_contra hi
    apply hn
    change raw q l hc (MixedWeightSupport.pure (fun j => Pi.single (p j) (v j))
      (fun j => Pi.single (s j) (w j))) = 0
    rw [raw_apply]
    have hh : leptonProjection (Pi.single (p i) (v i)) = 0 := by
      simp [leptonProjection, Pi.single_eq_of_ne (Ne.symm hi)]
    exact (localSeed.toLinearMap.comp
      ((TensorProduct.mk ℂ _ _).flip (SymmetricPower.tprod ℂ ((higgsProjection (k := k)) ∘ (fun j => Pi.single (s j) (w j)))))).compAlternatingMap
        (exteriorPower.ιMulti ℂ 2) |>.toMultilinearMap.map_coord_zero i hh
  have hy := BnvMixedInput.hypercharge_of_nonzero (ContentHiggsSupport.flavor q l) ContentHiggsSupport.scalar
    (raw q l hc) p s v w hn
  rw [ContentHiggsSupport.leptonPair_hyper p hp,DuqlHiggsContent.scalar_hypercharge] at hy
  have ht := DuqlHiggsContent.scalarCount_total s
  exact hs ⟨hp,by omega,by omega⟩

def seed (hc : 2*l=0) : ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 2 0 :=
  ⟨raw q l hc,supported q l hc⟩

theorem seed_nonzero (hc : 2*l=0) : seed q l hc ≠ 0 := by
  intro hz
  exact raw_nonzero q l hc (congrArg Subtype.val hz)

theorem seed_exists (hc : 2*l=0) :
    SelectionCriteria.Allowed (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 2 0) :=
  ⟨seed q l hc,seed_nonzero q l hc⟩


def localFermions : Fin 2 → LocalLepton :=
  ![(weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] 1,
    (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] 1]

theorem local_diagonal : localSeed (MixedWeightSupport.pure localFermions (fun _ => weakBasis 1))=1 := by
  have hN : WeinbergResidualHom.factorEquiv (trivial ℂ Unit ℂ)
      (WeinbergSMInterface.coefficientEquiv (trivial ℂ Unit ℂ) localSeed).val
        (1 ⊗ₜ[ℂ] 1)=1 :=
    WeinbergSMInterface.oneGenerationEquiv.apply_symm_apply 1
  have he := WeinbergSMInterface.coefficientEquiv_apply (trivial ℂ Unit ℂ) localSeed
    (weakBasis 0) (weakBasis 0) (weakBasis 0) (weakBasis 1) 1 1 (fun _ => weakBasis 1)
  change localSeed (exteriorPower.ιMulti ℂ 2 ![(weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] 1,
    (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] 1] ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => weakBasis 1))=1
  rw [← he,WeinbergResidualHom.reconstruction,hN]
  norm_num [WeinbergWeakInvariant.contraction_apply,eps2,weakBasis]

def boson : Bosons := (NeutralHiggsPowers.coordinates (H := CyclicCharge.Group k)).symm
  (weakBasis 1,LinearMap.proj 1)

omit [NeZero k] in
theorem boson_higgs : higgsProjection (k := k) (boson (k := k))=weakBasis 1 := by
  simp [higgsProjection,boson]

omit [NeZero k] in
theorem boson_normalized (r : ℕ) :
    NeutralHiggsPowers.normalized (H := CyclicCharge.Group k) r
      (SymmetricPower.tprod ℂ (fun _ => boson (k := k)))=1 := by
  rw [NeutralHiggsPowers.normalized_diagonal]
  simp [boson,weakBasis]

theorem raw_diagonal (hc : 2*l=0) : raw q l hc
    (MixedWeightSupport.pure (leptonInclusion ∘ localFermions) (fun _ => boson (k := k)))=1 := by
  rw [raw_apply]
  have hv : leptonProjection ∘ (leptonInclusion ∘ localFermions)=localFermions := by
    ext i; exact lepton_right_inverse _
  have hw : (higgsProjection (k := k)) ∘ (fun _ : Fin 2 => boson (k := k))=(fun _ => weakBasis 1) := by
    funext i; exact boson_higgs
  rw [hv,hw]
  exact local_diagonal


/-- Fermion support of the seed holds for arbitrary boson vectors. -/
theorem raw_fermion_zero (hc : 2*l=0) (p : Fin 2 → Species)
    (v : ∀ i, DeltaLOneSignedFields.Field
      (F := fun u => FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) (p i))
    (hp : ¬ ContentHiggsSupport.leptonPair p) (w : Fin 2 → Bosons) :
    raw q l hc (MixedWeightSupport.pure (fun i => Pi.single (p i) (v i)) w)=0 := by
  obtain ⟨i,hi⟩ : ∃ i, p i≠3 := by simpa only [ContentHiggsSupport.leptonPair,not_forall] using hp
  rw [raw_apply]
  have hh : leptonProjection (Pi.single (p i) (v i))=0 := by
    simp [leptonProjection,Pi.single_eq_of_ne (Ne.symm hi)]
  exact (localSeed.toLinearMap.comp
    ((TensorProduct.mk ℂ _ _).flip (SymmetricPower.tprod ℂ ((higgsProjection (k := k)) ∘ w)))).compAlternatingMap
      (exteriorPower.ιMulti ℂ 2) |>.toMultilinearMap.map_coord_zero i hh

def unshifted (hc : 2*l=0) (r : ℕ) : BnvMixedInput.Coefficient (ContentHiggsSupport.flavor q l)
    (ContentHiggsSupport.scalar (k := k)) 2 (2+r*2) :=
  SymmetricCoefficientDressing.product
    ((DeltaLOneSignedFields.fullRepresentation (ContentHiggsSupport.flavor q l)).exteriorPower 2)
    (NeutralHiggsPowers.action (H := CyclicCharge.Group k)) (raw q l hc)
    (NeutralHiggsPowers.normalized r)


theorem unshifted_diagonal (hc : 2*l=0) (r : ℕ) (v : Fin 2 → Fermions) (w : Bosons) :
    unshifted q l hc r (MixedWeightSupport.pure v (fun _ => w)) =
      raw q l hc (MixedWeightSupport.pure v (fun _ => w)) *
        NeutralHiggsPowers.normalized (H := CyclicCharge.Group k) r (SymmetricPower.tprod ℂ (fun _ => w)) := by
  exact SymmetricCoefficientDressing.product_diagonal _ _ _ _ _ _

theorem unshifted_apply (hc : 2*l=0) (r : ℕ) (v : Fin 2 → Fermions) (w : Fin (2+r*2) → Bosons) :
    unshifted q l hc r (MixedWeightSupport.pure v w) =
      (Nat.factorial (2+r*2) : ℂ)⁻¹ * ∑ e : Equiv.Perm (Fin (2+r*2)),
        raw q l hc (MixedWeightSupport.pure v
          (fun i => w (e (finSumFinEquiv (Sum.inl i))))) *
        NeutralHiggsPowers.normalized (H := CyclicCharge.Group k) r
          (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inr i))))) := by
  exact SymmetricCoefficientDressing.product_apply _ _ _ _ _ _

theorem unshifted_nonzero (hc : 2*l=0) (r : ℕ) : unshifted q l hc r ≠ 0 := by
  intro hz
  have he := congrArg (fun f => f (MixedWeightSupport.pure (leptonInclusion ∘ localFermions)
    (fun _ => boson (k := k)))) hz
  change unshifted q l hc r (MixedWeightSupport.pure (leptonInclusion ∘ localFermions)
    (fun _ => boson (k := k)))=0 at he
  rw [unshifted_diagonal,raw_diagonal,boson_normalized] at he
  norm_num at he

theorem unshifted_fermion_zero (hc : 2*l=0) (r : ℕ) (p : Fin 2 → Species)
    (v : ∀ i, DeltaLOneSignedFields.Field
      (F := fun u => FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) (p i))
    (hp : ¬ ContentHiggsSupport.leptonPair p) (w : Fin (2+r*2) → Bosons) :
    unshifted q l hc r (MixedWeightSupport.pure (fun i => Pi.single (p i) (v i)) w)=0 := by
  rw [unshifted_apply]
  have he : ∀ e : Equiv.Perm (Fin (2+r*2)),
      raw q l hc (MixedWeightSupport.pure (fun i => Pi.single (p i) (v i))
        (fun i => w (e (finSumFinEquiv (Sum.inl i)))))=0 := fun e => raw_fermion_zero q l hc p v hp _
  simp_rw [he]
  simp

def dressedRaw (hc : 2*l=0) (r : ℕ) : BnvMixedInput.Coefficient (ContentHiggsSupport.flavor q l)
    (ContentHiggsSupport.scalar (k := k)) 2 ((r+2)+r) := by
  have e : 2+r*2=(r+2)+r := by omega
  exact e ▸ unshifted q l hc r

theorem dressedRaw_nonzero (hc : 2*l=0) (r : ℕ) : dressedRaw q l hc r ≠ 0 := by
  let T (m : ℕ) := BnvMixedInput.Coefficient (ContentHiggsSupport.flavor q l)
    (ContentHiggsSupport.scalar (k := k)) 2 m
  have transport (n m : ℕ) (e : n=m) (f : T n) (hf : f≠0) : (e ▸ f : T m) ≠ 0 := by subst m; exact hf
  exact transport _ _ (by omega) _ (unshifted_nonzero q l hc r)

theorem dressedRaw_mem (hc : 2*l=0) (r : ℕ) : dressedRaw q l hc r ∈
    ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair (r+2) r := by
  intro p s hs v w
  by_contra hn
  have hf : ∀ (m : ℕ) (e : 2+r*2=m) (ww : Fin m → Bosons),
      (e ▸ unshifted q l hc r : BnvMixedInput.Coefficient (ContentHiggsSupport.flavor q l)
        (ContentHiggsSupport.scalar (k := k)) 2 m)
        (MixedWeightSupport.pure (fun i => Pi.single (p i) (v i)) ww) ≠ 0 → ContentHiggsSupport.leptonPair p := by
    intro m e ww hh
    subst m
    by_contra hp
    exact hh (unshifted_fermion_zero q l hc r p v hp ww)
  have hp : ContentHiggsSupport.leptonPair p := hf _ (by omega) _ hn
  have hy := BnvMixedInput.hypercharge_of_nonzero (ContentHiggsSupport.flavor q l) ContentHiggsSupport.scalar
    (dressedRaw q l hc r) p s v w hn
  rw [ContentHiggsSupport.leptonPair_hyper p hp,DuqlHiggsContent.scalar_hypercharge] at hy
  have ht := DuqlHiggsContent.scalarCount_total s
  exact hs ⟨hp,by omega,by omega⟩

def dressed (hc : 2*l=0) (r : ℕ) : ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair (r+2) r :=
  ⟨dressedRaw q l hc r,dressedRaw_mem q l hc r⟩

theorem dressed_nonzero (hc : 2*l=0) (r : ℕ) : dressed q l hc r ≠ 0 := by
  intro hz
  exact dressedRaw_nonzero q l hc r (congrArg Subtype.val hz)

theorem allowed_iff (h a : ℕ) : SelectionCriteria.Allowed
    (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair h a) ↔ h=a+2 ∧ 2*l=0 := by
  constructor
  · exact ContentHiggsSupport.leptonPair_necessary q l h a
  · rintro ⟨rfl,hc⟩
    exact ⟨dressed q l hc a,dressed_nonzero q l hc a⟩


theorem forbidden_iff (h a : ℕ) : SelectionCriteria.Forbidden
    (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair h a) ↔ h≠a+2 ∨ 2*l≠0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]
  exact not_and_or

theorem all_forbidden_iff :
    (∀ h a, SelectionCriteria.Forbidden (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair h a)) ↔ 2*l≠0 := by
  constructor
  · intro hh hc
    obtain ⟨f,hf⟩ := seed_exists q l hc
    exact hf (hh 2 0 f)
  · intro hc h a
    rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]
    exact fun hh => hc hh.2

end
end GUT.WeinbergFullSeed
