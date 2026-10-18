import GUT.SU5.SelectionRules.MixedTenMass
import Physics.FieldTheory.Mass.CommonCopyKernel
import Physics.FieldTheory.Mass.AlgebraicCommonCopyKernel
import Mathlib.RingTheory.Flat.Basic
import Physics.StandardModel.Operators.PhysicalQqueEndpoint

/-! Non-scalar common residual copy representations on actual SU(5) tens.
Species kernels inject equivariantly into the actual Dirac mass radical. -/
namespace GUT.SU5.NonScalarCopyMass
set_option autoImplicit false
noncomputable section
open Math Representation StandardModelEmbedding Matter ExteriorSquareBranching
open StandardSMGaugeTensor SMEpsilonTensor InvariantWeylMass MixedTenMass
open ExternalInvariantTensor ContinuousRepresentationScope CompactEmbeddingClassification
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance
universe u
variable {H : Type*} [Group H] {S T : Type u}

section Algebraic
variable [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T)

def externalMap {G V W A B : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {r : Representation ℂ G V} {r' : Representation ℂ G W}
    {a : Representation ℂ H A} {b : Representation ℂ H B}
    (f : IntertwiningMap r r') (k : IntertwiningMap a b) :
    IntertwiningMap (external r a) (external r' b) where
  toLinearMap := TensorProduct.map f.toLinearMap k.toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change f (r g.1 x) ⊗ₜ[ℂ] k (a g.2 y) = r' g.1 (f x) ⊗ₜ[ℂ] b g.2 (k y)
    rw [f.isIntertwining _ _ g.1, k.isIntertwining _ _ g.2]

abbrev Source := (Ten ⊗[ℂ] S) × BarFive
abbrev Target := Ten ⊗[ℂ] T
abbrev Fields := Source (S := S) × Module.Dual ℂ (Target (T := T))

def barAction (psi : H →* Circle) : Representation ℂ (GaugeGroup × H) BarFive where
  toFun g := (psi g.2 : ℂ) • antifundamental (hom g.1)
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    simp [map_mul, smul_smul, mul_comm]


def sourceRho (psi : H →* Circle) := (external (ten.comp hom) s).prod (barAction psi)
def targetRho := external (ten.comp hom) t
def fieldsRho (psi : H →* Circle) := (sourceRho s psi).prod (targetRho t).dual

def upWeight : RowWeights := ⟨1,0,0⟩
def quarkWeight : RowWeights := ⟨0,1,0⟩
def electronWeight : RowWeights := ⟨0,0,1⟩

def massMap (psi : H →* Circle) (Mq Mu Me : IntertwiningMap s t) :
    IntertwiningMap (sourceRho s psi) (targetRho t) :=
  (externalMap (weighted quarkWeight) Mq + externalMap (weighted upWeight) Mu +
    externalMap (weighted electronWeight) Me).comp
      (IntertwiningMap.fst ℂ (external (ten.comp hom) s) (barAction psi))

def mass (psi : H →* Circle) (Mq Mu Me : IntertwiningMap s t) := ofDirac (massMap s t psi Mq Mu Me)

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem mem_radical_iff (psi : H →* Circle) (Mq Mu Me : IntertwiningMap s t)
    (x : Fields (S := S) (T := T)) :
    x ∈ (mass s t psi Mq Mu Me).radical.toSubmodule ↔
      massMap s t psi Mq Mu Me x.1 = 0 ∧ ∀ v, x.2 (massMap s t psi Mq Mu Me v) = 0 :=
  DiracWeylConvention.mem_radical_iff _ _

variable (Mq Mu Me : IntertwiningMap s t)

def kernelInclusion (M : IntertwiningMap s t) : IntertwiningMap M.ker.toRepresentation s :=
  CharacterExact.subtypeIntertwiner M.ker


def quarkTenMap : IntertwiningMap quark (ten.comp hom) where
  toLinearMap := quarkTen
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (quarkTen_action g x).symm

def quarkEmbedding (psi : H →* Circle) :
    IntertwiningMap (external quark Mq.ker.toRepresentation) (fieldsRho s t psi) :=
  (IntertwiningMap.inl ℂ (sourceRho s psi) (targetRho t).dual).comp
    ((IntertwiningMap.inl ℂ (external (ten.comp hom) s) (barAction psi)).comp
      (externalMap quarkTenMap (kernelInclusion s t Mq)))

omit [FiniteDimensional ℂ T] in
theorem quark_injective (psi : H →* Circle) : Function.Injective (quarkEmbedding s t Mq psi) := by
  intro x y he
  have ht := congrArg (fun z : Fields (S := S) (T := T) => z.1.1) he
  exact TensorProduct.map_injective_of_flat_flat quarkTen (kernelInclusion s t Mq).toLinearMap
    quarkTen_injective Subtype.val_injective ht

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem quark_light (psi : H →* Circle) (x : Quark ⊗[ℂ] Mq.ker.toSubmodule) :
    quarkEmbedding s t Mq psi x ∈ (mass s t psi Mq Mu Me).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · induction x using TensorProduct.inductionOn with
    | tmul v w =>
      change ((weighted quarkWeight) (quarkTen v) ⊗ₜ[ℂ] Mq w.val +
        (weighted upWeight) (quarkTen v) ⊗ₜ[ℂ] Mu w.val +
        (weighted electronWeight) (quarkTen v) ⊗ₜ[ℂ] Me w.val) = 0
      have hz : Mq w.val = 0 := w.property
      simp [quark_weighted, quarkWeight, upWeight, electronWeight, hz]
    | add x y hx hy =>
      change massMap s t psi Mq Mu Me ((quarkEmbedding s t Mq psi) (x+y)).1 = 0
      simp only [map_add, Prod.fst_add, hx, hy, add_zero]
  · intro v
    change (0 : Module.Dual ℂ (Target (T := T))) (massMap s t psi Mq Mu Me v) = 0
    rfl

def upTenMap : IntertwiningMap upRight.dual (ten.comp hom) where
  toLinearMap := upTen
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (upTen_action g x).symm

def upEmbedding (psi : H →* Circle) :
    IntertwiningMap (external upRight.dual Mu.ker.toRepresentation) (fieldsRho s t psi) :=
  (IntertwiningMap.inl ℂ (sourceRho s psi) (targetRho t).dual).comp
    ((IntertwiningMap.inl ℂ (external (ten.comp hom) s) (barAction psi)).comp
      (externalMap upTenMap (kernelInclusion s t Mu)))

omit [FiniteDimensional ℂ T] in
theorem up_injective (psi : H →* Circle) : Function.Injective (upEmbedding s t Mu psi) := by
  intro x y he
  have ht := congrArg (fun z : Fields (S := S) (T := T) => z.1.1) he
  exact TensorProduct.map_injective_of_flat_flat upTen (kernelInclusion s t Mu).toLinearMap
    upTen_injective Subtype.val_injective ht

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem up_light (psi : H →* Circle) (x : Module.Dual ℂ Color ⊗[ℂ] Mu.ker.toSubmodule) :
    upEmbedding s t Mu psi x ∈ (mass s t psi Mq Mu Me).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · induction x using TensorProduct.inductionOn with
    | tmul v w =>
      change ((weighted quarkWeight) (upTen v) ⊗ₜ[ℂ] Mq w.val +
        (weighted upWeight) (upTen v) ⊗ₜ[ℂ] Mu w.val +
        (weighted electronWeight) (upTen v) ⊗ₜ[ℂ] Me w.val) = 0
      have hz : Mu w.val = 0 := w.property
      simp [up_weighted, quarkWeight, upWeight, electronWeight, hz]
    | add x y hx hy =>
      change massMap s t psi Mq Mu Me ((upEmbedding s t Mu psi) (x+y)).1 = 0
      simp only [map_add, Prod.fst_add, hx, hy, add_zero]
  · intro v
    change (0 : Module.Dual ℂ (Target (T := T))) (massMap s t psi Mq Mu Me v) = 0
    rfl

def electronTenMap : IntertwiningMap electronRight.dual (ten.comp hom) where
  toLinearMap := electronTen
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (electronTen_action g x).symm

def electronEmbedding (psi : H →* Circle) :
    IntertwiningMap (external electronRight.dual Me.ker.toRepresentation) (fieldsRho s t psi) :=
  (IntertwiningMap.inl ℂ (sourceRho s psi) (targetRho t).dual).comp
    ((IntertwiningMap.inl ℂ (external (ten.comp hom) s) (barAction psi)).comp
      (externalMap electronTenMap (kernelInclusion s t Me)))

omit [FiniteDimensional ℂ T] in
theorem electron_injective (psi : H →* Circle) : Function.Injective (electronEmbedding s t Me psi) := by
  intro x y he
  have ht := congrArg (fun z : Fields (S := S) (T := T) => z.1.1) he
  exact TensorProduct.map_injective_of_flat_flat electronTen (kernelInclusion s t Me).toLinearMap
    electronTen_injective Subtype.val_injective ht

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem electron_light (psi : H →* Circle) (x : Module.Dual ℂ ℂ ⊗[ℂ] Me.ker.toSubmodule) :
    electronEmbedding s t Me psi x ∈ (mass s t psi Mq Mu Me).radical.toSubmodule := by
  rw [mem_radical_iff]
  constructor
  · induction x using TensorProduct.inductionOn with
    | tmul v w =>
      change ((weighted quarkWeight) (electronTen v) ⊗ₜ[ℂ] Mq w.val +
        (weighted upWeight) (electronTen v) ⊗ₜ[ℂ] Mu w.val +
        (weighted electronWeight) (electronTen v) ⊗ₜ[ℂ] Me w.val) = 0
      have hz : Me w.val = 0 := w.property
      simp [electron_weighted, quarkWeight, upWeight, electronWeight, hz]
    | add x y hx hy =>
      change massMap s t psi Mq Mu Me ((electronEmbedding s t Me psi) (x+y)).1 = 0
      simp only [map_add, Prod.fst_add, hx, hy, add_zero]
  · intro v
    change (0 : Module.Dual ℂ (Target (T := T))) (massMap s t psi Mq Mu Me v) = 0
    rfl

section ExternalDual
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def dualExternalEquiv (r : Representation ℂ G V) (a : Representation ℂ H W) :
    Representation.Equiv (external r.dual a.dual) (external r a).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ V W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro phi psi
    apply TensorProduct.ext'
    intro x y
    rfl

end ExternalDual

variable (psi : H →* Circle)

def rangeCoords {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] Fields (S := S) (T := T)) (hf : Function.Injective f) :
    LinearMap.range f ≃ₗ[ℂ] V := (LinearEquiv.ofInjective f hf).symm

def rangeRho {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ (GaugeGroup × H) V)
    (f : IntertwiningMap r (fieldsRho s t psi)) (hf : Function.Injective f) :=
  RepresentationConjugation.pullback (rangeCoords f.toLinearMap hf) r

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem range_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ (GaugeGroup × H) V)
    (f : IntertwiningMap r (fieldsRho s t psi)) (hf : Function.Injective f)
    (g : GaugeGroup × H) (x : LinearMap.range f.toLinearMap) :
    (rangeRho s t psi r f hf g x).val = fieldsRho s t psi g x.val := by
  rw [rangeRho, RepresentationConjugation.pullback_apply]
  change f (r g (rangeCoords f.toLinearMap hf x)) = _
  rw [f.isIntertwining _ _ g]
  have he := congrArg Subtype.val ((rangeCoords f.toLinearMap hf).symm_apply_apply x)
  change f (rangeCoords f.toLinearMap hf x) = x.val at he
  rw [he]

abbrev QuarkSpace := LinearMap.range (quarkEmbedding s t Mq psi).toLinearMap
abbrev UpSpace := LinearMap.range (upEmbedding s t Mu psi).toLinearMap
abbrev ElectronSpace := LinearMap.range (electronEmbedding s t Me psi).toLinearMap

local instance : AddCommGroup (QuarkSpace s t Mq psi) := inferInstance
local instance : AddCommGroup (UpSpace s t Mu psi) := inferInstance
local instance : AddCommGroup (ElectronSpace s t Me psi) := inferInstance

def quarkRho := rangeRho s t psi _ (quarkEmbedding s t Mq psi) (quark_injective s t Mq psi)
def upLeftRho := rangeRho s t psi _ (upEmbedding s t Mu psi) (up_injective s t Mu psi)
def electronLeftRho := rangeRho s t psi _ (electronEmbedding s t Me psi) (electron_injective s t Me psi)

def quarkEq : Representation.Equiv (quarkRho s t Mq psi)
    (QqueSpinorExterior.qField (a := Mq.ker.toRepresentation)) :=
  RepresentationConjugation.equiv _ _

def upEq : Representation.Equiv (upLeftRho s t Mu psi).dual
    (QqueSpinorExterior.uField (b := Mu.ker.toRepresentation)) :=
  (SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv upRight.dual Mu.ker.toRepresentation).symm.trans
      (externalEquiv (SplitRepresentationProjection.bidualEquiv upRight).symm
        (Representation.Equiv.refl _)))

def electronEq : Representation.Equiv (electronLeftRho s t Me psi).dual
    (QqueSpinorExterior.eField (d := Me.ker.toRepresentation)) :=
  (SplitRepresentationProjection.dualEquiv
    (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv electronRight.dual Me.ker.toRepresentation).symm.trans
      (externalEquiv (SplitRepresentationProjection.bidualEquiv electronRight).symm
        (Representation.Equiv.refl _)))


/-- Algebraic endpoint for any group, with semisimple source only. -/
theorem exists_actual_exterior_of_semisimple (hss : IsSemisimpleRepresentation s)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨c,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ :=
    AlgebraicCommonCopyKernel.exists_common_split s t hss Mq Mu Me hd
  let : Nontrivial (AlgebraicCommonCopyKernel.Carrier s c) := hn
  apply PhysicalQqueEndpoint.of_alternation
  exact QqueSpinorExterior.exists_on_fields sq su se
    (quarkRho s t Mq psi) (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual
    (quarkEq s t Mq psi) (upEq s t Mu psi) (electronEq s t Me psi)

theorem exists_light_exterior_of_semisimple (hss : IsSemisimpleRepresentation s)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    (∀ x : QuarkSpace s t Mq psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : UpSpace s t Mu psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : ElectronSpace s t Me psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  refine ⟨?_,?_,?_,exists_actual_exterior_of_semisimple s t Mq Mu Me psi hss hd⟩
  · rintro ⟨x,y,rfl⟩; exact quark_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact up_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact electron_light s t Mq Mu Me psi y

end Algebraic

section Analytic
variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
  (s : Representation ℂ H S) (t : Representation ℂ H T)
  (Mq Mu Me : IntertwiningMap s t) (psi : H →* Circle)
local instance : AddCommGroup (QuarkSpace s t Mq psi) := inferInstance
local instance : AddCommGroup (UpSpace s t Mu psi) := inferInstance
local instance : AddCommGroup (ElectronSpace s t Me psi) := inferInstance

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hs : IsJointlyContinuous s) (ht : IsJointlyContinuous t) (hu : IsUnitaryRepresentation t)

include hs ht hu in
/-- Physical coefficient on the actual typed kernel multiplicities. The
left-handed species have derived injective maps into the actual mass radical. -/
theorem kernel_physical_exterior (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    QqueSpinorExterior.HasModelExterior (a := Mq.ker.toRepresentation)
      (b := Mu.ker.toRepresentation) (d := Me.ker.toRepresentation) :=
  CommonCopyKernel.kernel_physical_exterior s t hs ht hu Mq Mu Me hd

include hs ht hu in
theorem exists_actual_exterior (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨i, hn, ⟨sq⟩, ⟨su⟩, ⟨se⟩⟩ := CommonCopyKernel.exists_common_split s t hs ht hu Mq Mu Me hd
  let : Nontrivial ((CommonCopyKernel.presentation s t hs ht).Carrier i) := hn
  apply PhysicalQqueEndpoint.of_alternation
  exact (QqueSpinorExterior.exists_on_fields sq su se
    (quarkRho s t Mq psi) (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual
    (quarkEq s t Mq psi) (upEq s t Mu psi) (electronEq s t Me psi))

include hs ht hu in
theorem exists_light_exterior (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    (∀ x : QuarkSpace s t Mq psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : UpSpace s t Mu psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : ElectronSpace s t Me psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  refine ⟨?_,?_,?_,exists_actual_exterior s t Mq Mu Me psi hs ht hu hd⟩
  · rintro ⟨x,y,rfl⟩; exact quark_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact up_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact electron_light s t Mq Mu Me psi y


include hs ht in
/-- Physical coefficient on original participating ranges, without supplied
unitarity for the original target metric. -/
theorem exists_actual_exterior_of_continuous
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  obtain ⟨i,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ :=
    CommonCopyKernel.exists_common_split_of_continuous s t hs ht Mq Mu Me hd
  let : Nontrivial ((CommonCopyKernel.presentation s (CommonCopyKernel.unitaryTarget t ht)
    hs (CommonCopyKernel.unitaryTarget_continuous t ht)).Carrier i) := hn
  apply PhysicalQqueEndpoint.of_alternation
  exact QqueSpinorExterior.exists_on_fields sq su se
    (quarkRho s t Mq psi) (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual
    (quarkEq s t Mq psi) (upEq s t Mu psi) (electronEq s t Me psi)

include hs ht in
theorem exists_light_exterior_of_continuous
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    (∀ x : QuarkSpace s t Mq psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : UpSpace s t Mu psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    (∀ x : ElectronSpace s t Me psi, x.val ∈ (mass s t psi Mq Mu Me).radical.toSubmodule) ∧
    PhysicalQqueEndpoint.HasExterior (quarkRho s t Mq psi)
      (upLeftRho s t Mu psi).dual (electronLeftRho s t Me psi).dual := by
  refine ⟨?_,?_,?_,exists_actual_exterior_of_continuous s t Mq Mu Me psi hs ht hd⟩
  · rintro ⟨x,y,rfl⟩; exact quark_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact up_light s t Mq Mu Me psi y
  · rintro ⟨x,y,rfl⟩; exact electron_light s t Mq Mu Me psi y

end Analytic

end
end GUT.SU5.NonScalarCopyMass
