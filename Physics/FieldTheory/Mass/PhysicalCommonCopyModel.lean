import Physics.FieldTheory.Mass.AlgebraicCommonCopyKernel
import Physics.FieldTheory.Mass.InvariantWeylMass
import Physics.StandardModel.Operators.PhysicalQqueEndpoint
import Mathlib.RingTheory.Flat.Basic
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

/-! Model-independent actual-field realization of the common-copy obstruction.
Mass factorization is structural input; light support and a physical exterior
coefficient are conclusions. No unified gauge group or fixed matter carrier enters. -/
namespace GUT.PhysicalCommonCopyModel
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor StandardSMGaugeTensor
open SplitRepresentationProjection InvariantWeylMass
open scoped TensorProduct
variable {H S T F : Type*} [Group H]
  [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  [AddCommGroup F] [Module ℂ F]
  {s : Representation ℂ H S} {t : Representation ℂ H T}
  {rho : Representation ℂ (GaugeGroup × H) F}

/-- Tensor an actual gauge intertwiner with a copy intertwiner. -/
def externalMap {G V W A C : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C]
    {r : Representation ℂ G V} {r' : Representation ℂ G W}
    {a : Representation ℂ H A} {b : Representation ℂ H C}
    (f : IntertwiningMap r r') (k : IntertwiningMap a b) :
    IntertwiningMap (external r a) (external r' b) where
  toLinearMap := TensorProduct.map f.toLinearMap k.toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change f (r g.1 x) ⊗ₜ[ℂ] k (a g.2 y) = r' g.1 (f x) ⊗ₜ[ℂ] b g.2 (k y)
    rw [f.isIntertwining _ _ g.1, k.isIntertwining _ _ g.2]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (r : Representation ℂ GaugeGroup V) (B : SymmetricMass rho)

/-- A mass commuting square on a full species sector. It does not assume
that any participating field is light, or that a qque coefficient exists. -/
structure Species where
  map : IntertwiningMap s t
  embed : IntertwiningMap (external r s) rho
  injective : Function.Injective embed
  dualField : IntertwiningMap (external r t) rho.dual
  mass_square : B.toIntertwiningMap.comp embed =
    dualField.comp (externalMap (IntertwiningMap.id r) map)

namespace Species
variable {r B} (X : Species (s := s) (t := t) r B)

def lightEmbedding : IntertwiningMap (external r X.map.ker.toRepresentation) rho :=
  X.embed.comp (externalMap (IntertwiningMap.id r)
    (CharacterExact.subtypeIntertwiner X.map.ker))

omit [FiniteDimensional ℂ T] in
theorem light_injective : Function.Injective X.lightEmbedding := by
  apply X.injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id Subtype.val_injective

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem light_mem_radical (x : V ⊗[ℂ] X.map.ker.toSubmodule) :
    X.lightEmbedding x ∈ B.radical.toSubmodule := by
  change B.toIntertwiningMap (X.lightEmbedding x) = 0
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    have he := congrArg (fun f : IntertwiningMap (external r s) rho.dual =>
      f (v ⊗ₜ[ℂ] (w.val : S))) X.mass_square
    change B.toIntertwiningMap (X.lightEmbedding (v ⊗ₜ[ℂ] w)) = _ at he
    rw [he]
    change X.dualField (v ⊗ₜ[ℂ] X.map w.val) = 0
    have hz : X.map w.val = 0 := w.property
    simp [hz]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

def rangeCoords : LinearMap.range X.lightEmbedding.toLinearMap ≃ₗ[ℂ]
    V ⊗[ℂ] X.map.ker.toSubmodule :=
  (LinearEquiv.ofInjective X.lightEmbedding.toLinearMap X.light_injective).symm

def rangeRho := RepresentationConjugation.pullback X.rangeCoords
  (external r X.map.ker.toRepresentation)

omit [FiniteDimensional ℂ T] in
theorem range_action (g : GaugeGroup × H)
    (x : LinearMap.range X.lightEmbedding.toLinearMap) :
    (X.rangeRho g x).val = rho g x.val := by
  rw [rangeRho, RepresentationConjugation.pullback_apply]
  change X.lightEmbedding ((external r X.map.ker.toRepresentation) g (X.rangeCoords x)) = _
  rw [X.lightEmbedding.isIntertwining _ _ g]
  have he := congrArg Subtype.val (X.rangeCoords.symm_apply_apply x)
  change X.lightEmbedding (X.rangeCoords x) = x.val at he
  rw [he]

omit [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
theorem range_light (x : LinearMap.range X.lightEmbedding.toLinearMap) :
    x.val ∈ B.radical.toSubmodule := by
  rcases x with ⟨x,y,rfl⟩
  exact X.light_mem_radical y

end Species

section DiracConstructor
variable {A C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  {a : Representation ℂ (GaugeGroup × H) A}
  {c : Representation ℂ (GaugeGroup × H) C}

/-- A derived Dirac normal form and a species commuting diagram realize
an arbitrary original symmetric mass. No light-field certificate is supplied. -/
def speciesOfDirac (M : IntertwiningMap a c)
    (B : SymmetricMass (a.prod c.dual))
    (hB : B.form = (ofDirac M).form)
    (m : IntertwiningMap s t)
    (i : IntertwiningMap (external r s) a) (hi : Function.Injective i)
    (j : IntertwiningMap (external r t) c)
    (hM : M.comp i = j.comp (externalMap (IntertwiningMap.id r) m)) :
    Species (s := s) (t := t) r B where
  map := m
  embed := (IntertwiningMap.inl ℂ a c.dual).comp i
  injective := by
    intro x y he
    exact hi (congrArg Prod.fst he)
  dualField := (dualMap (IntertwiningMap.snd ℂ a c.dual)).comp
    ((bidualEquiv c).toIntertwiningMap.comp j)
  mass_square := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change B.form (i x, 0) y = y.2 (j ((externalMap (IntertwiningMap.id r) m) x))
    rw [hB]
    change y.2 (M (i x)) + (0 : Module.Dual ℂ C) (M y.1) = _
    have he := congrArg (fun f : IntertwiningMap (external r s) c => f x) hM
    change M (i x) = j ((externalMap (IntertwiningMap.id r) m) x) at he
    simp only [he, LinearMap.zero_apply, add_zero]
end DiracConstructor

/-- The three physical species share S and T, but their mass maps may differ. -/
structure Realization (B : SymmetricMass rho) where
  q : Species (s := s) (t := t) StandardSMGaugeTensor.quark B
  u : Species (s := s) (t := t) StandardSMGaugeTensor.upRight.dual B
  e : Species (s := s) (t := t) StandardSMGaugeTensor.electronRight.dual B

section ExternalDual
variable {G A C : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]

def dualExternalEquiv (a : Representation ℂ G A) (b : Representation ℂ H C) :
    Representation.Equiv (external a.dual b.dual) (external a b).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ A C
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro phi psi
    apply TensorProduct.ext'
    intro x y
    rfl
end ExternalDual

namespace Realization
variable {B : SymmetricMass rho} (X : Realization (s := s) (t := t) B)
local instance : AddCommGroup (LinearMap.range X.q.lightEmbedding.toLinearMap) := inferInstance
local instance : AddCommGroup (LinearMap.range X.u.lightEmbedding.toLinearMap) := inferInstance
local instance : AddCommGroup (LinearMap.range X.e.lightEmbedding.toLinearMap) := inferInstance

def quarkEq : Representation.Equiv X.q.rangeRho
    (QqueSpinorExterior.qField (a := X.q.map.ker.toRepresentation)) :=
  RepresentationConjugation.equiv _ _

def upEq : Representation.Equiv X.u.rangeRho.dual
    (QqueSpinorExterior.uField (b := X.u.map.ker.toRepresentation)) :=
  (dualEquiv (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv StandardSMGaugeTensor.upRight.dual X.u.map.ker.toRepresentation).symm.trans
      (externalEquiv (bidualEquiv StandardSMGaugeTensor.upRight).symm (Representation.Equiv.refl _)))

def electronEq : Representation.Equiv X.e.rangeRho.dual
    (QqueSpinorExterior.eField (d := X.e.map.ker.toRepresentation)) :=
  (dualEquiv (RepresentationConjugation.equiv _ _)).trans
    ((dualExternalEquiv StandardSMGaugeTensor.electronRight.dual X.e.map.ker.toRepresentation).symm.trans
      (externalEquiv (bidualEquiv StandardSMGaugeTensor.electronRight).symm (Representation.Equiv.refl _)))

/-- Actual participating ranges are light and carry a physical exterior
coefficient; right-handed species use the duals of actual left-handed ranges. -/
def HasLightExterior : Prop :=
  (∀ x : LinearMap.range X.q.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  (∀ x : LinearMap.range X.u.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  (∀ x : LinearMap.range X.e.lightEmbedding.toLinearMap, x.val ∈ B.radical.toSubmodule) ∧
  PhysicalQqueEndpoint.HasExterior X.q.rangeRho X.u.rangeRho.dual X.e.rangeRho.dual

/-- Model-independent physical consequence of source semisimplicity and
positive common-copy dimension difference. No topology or GUT group is used. -/
theorem light_exterior (hs : IsSemisimpleRepresentation s)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) : X.HasLightExterior := by
  obtain ⟨c,hn,⟨sq⟩,⟨su⟩,⟨se⟩⟩ := AlgebraicCommonCopyKernel.exists_common_split
    s t hs X.q.map X.u.map X.e.map hd
  let : Nontrivial (AlgebraicCommonCopyKernel.Carrier s c) := hn
  refine ⟨X.q.range_light, X.u.range_light, X.e.range_light, ?_⟩
  apply PhysicalQqueEndpoint.of_alternation
  exact QqueSpinorExterior.exists_on_fields sq su se
    X.q.rangeRho X.u.rangeRho.dual X.e.rangeRho.dual X.quarkEq X.upEq X.electronEq
end Realization

/-- A matter/action model derives the structural realization for every
invariant symmetric mass. This classification obligation is model-specific. -/
structure Model (s : Representation ℂ H S) (t : Representation ℂ H T)
    (rho : Representation ℂ (GaugeGroup × H) F) where
  realize : (B : SymmetricMass rho) → Realization (s := s) (t := t) B

/-- A reusable arbitrary-mass endpoint on the original field carrier. -/
theorem Model.arbitrary_mass_light_exterior (X : Model s t rho)
    (B : SymmetricMass rho) (hs : IsSemisimpleRepresentation s)
    (hd : Module.finrank ℂ T < Module.finrank ℂ S) :
    (X.realize B).HasLightExterior :=
  (X.realize B).light_exterior hs hd

end
end GUT.PhysicalCommonCopyModel
