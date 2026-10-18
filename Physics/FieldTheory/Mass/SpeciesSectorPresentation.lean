import Physics.FieldTheory.Mass.PhysicalSpeciesCopySurplus
import Physics.FieldTheory.Mass.BipartiteNormalForm
import Math.RepresentationTheory.Decomposition.ExternalCopyFactorization

/-! A supplied sector decomposition and gauge-pairing conditions derive species
mass maps from every original symmetric mass. The complementary sector is arbitrary. -/
namespace GUT.SpeciesSectorPresentation
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor StandardSMGaugeTensor
open InvariantWeylMass SplitRepresentationProjection PhysicalCommonCopyModel
open BipartiteNormalForm
open scoped TensorProduct
variable {H V A C Z F : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  [AddCommGroup Z] [Module ℂ Z] [AddCommGroup F] [Module ℂ F]
  (r : Representation ℂ GaugeGroup V) (a : Representation ℂ H A)
  (c : Representation ℂ H C) (z : Representation ℂ (GaugeGroup × H) Z)
  (rho : Representation ℂ (GaugeGroup × H) F)

/-- Conditions concern the supplied full sector, not a mass or light spectrum.
Factorization is a gauge-pairing interface valid for every intertwiner. -/
structure Presentation where
  coordinates : Representation.Equiv rho ((external r a).prod ((external r c).dual.prod z))
  noSelf : NoPairings (external r a) (external r a)
  noRest : NoPairings (external r a) z
  factor : ∀ M : IntertwiningMap (external r a) (external r c),
    ∃ m : IntertwiningMap a c, M = externalMap (IntertwiningMap.id r) m

/-- Gauge irreducibility derives factorization for arbitrary residual copy
actions. No factorization or mass normal form is supplied for a chosen B. -/
def ofIrreducible [IsIrreducible r]
    (coordinates : Representation.Equiv rho ((external r a).prod ((external r c).dual.prod z)))
    (noSelf : NoPairings (external r a) (external r a))
    (noRest : NoPairings (external r a) z) : Presentation r a c z rho where
  coordinates := coordinates
  noSelf := noSelf
  noRest := noRest
  factor M := by
    obtain ⟨m,hm⟩ := ExternalCopyFactorization.exists_copy_map r a c M
    refine ⟨m, ?_⟩
    apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro v x
    exact hm v x

namespace Presentation
variable {r a c z rho} (P : Presentation r a c z rho)

def source : IntertwiningMap (external r a) rho :=
  P.coordinates.symm.toIntertwiningMap.comp (IntertwiningMap.inl ℂ _ _)

def opposite : IntertwiningMap (external r c).dual rho :=
  P.coordinates.symm.toIntertwiningMap.comp
    ((IntertwiningMap.inr ℂ _ _).comp (IntertwiningMap.inl ℂ _ _))

def rest : IntertwiningMap z rho :=
  P.coordinates.symm.toIntertwiningMap.comp
    ((IntertwiningMap.inr ℂ _ _).comp (IntertwiningMap.inr ℂ _ _))

def oppositeProjection : IntertwiningMap rho (external r c).dual :=
  ((IntertwiningMap.fst ℂ _ _).comp (IntertwiningMap.snd ℂ _ _)).comp
    P.coordinates.toIntertwiningMap

def rawMass (B : SymmetricMass rho) :
    IntertwiningMap (external r a) (external r c).dual.dual :=
  (dualMap P.opposite).comp (B.toIntertwiningMap.comp P.source)

def massMap (B : SymmetricMass rho) : IntertwiningMap (external r a) (external r c) :=
  (bidualEquiv (external r c)).symm.toIntertwiningMap.comp (P.rawMass B)

def dualField : IntertwiningMap (external r c) rho.dual :=
  (dualMap P.oppositeProjection).comp (bidualEquiv (external r c)).toIntertwiningMap

omit [FiniteDimensional ℂ A] in
/-- No same-side/rest pairing makes the full original mass column factor
through the opposite sector. No global Dirac normal form is imposed. -/
theorem mass_column (B : SymmetricMass rho) :
    B.toIntertwiningMap.comp P.source = P.dualField.comp (P.massMap B) := by
  have hself := P.noSelf ((dualMap P.source).comp (B.toIntertwiningMap.comp P.source))
  have hrest := P.noRest ((dualMap P.rest).comp (B.toIntertwiningMap.comp P.source))
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hz1 : B.form (P.source x) (P.source (P.coordinates y).1) = 0 :=
    LinearMap.congr_fun (DFunLike.congr_fun hself x) (P.coordinates y).1
  have hz3 : B.form (P.source x) (P.rest (P.coordinates y).2.2) = 0 :=
    LinearMap.congr_fun (DFunLike.congr_fun hrest x) (P.coordinates y).2.2
  have hy : y = P.source (P.coordinates y).1 +
      P.opposite (P.coordinates y).2.1 + P.rest (P.coordinates y).2.2 := by
    apply P.coordinates.toLinearEquiv.injective
    change P.coordinates y = P.coordinates
      (P.coordinates.symm ((P.coordinates y).1, 0) +
       P.coordinates.symm (0, ((P.coordinates y).2.1, 0)) +
       P.coordinates.symm (0, (0, (P.coordinates y).2.2)))
    simp only [map_add, P.coordinates.apply_symm_apply]
    ext <;> simp
  change B.form (P.source x) y = P.dualField (P.massMap B x) y
  have hr : P.dualField (P.massMap B x) y =
      B.form (P.source x) (P.opposite (P.coordinates y).2.1) := by
    change (P.oppositeProjection y) (P.massMap B x) = _
    have he := (bidualEquiv (external r c)).toLinearEquiv.apply_symm_apply (P.rawMass B x)
    have hv := LinearMap.congr_fun he (P.oppositeProjection y)
    exact hv
  rw [hr]
  calc
    B.form (P.source x) y = B.form (P.source x)
        (P.source (P.coordinates y).1 + P.opposite (P.coordinates y).2.1 +
          P.rest (P.coordinates y).2.2) := congrArg (B.form (P.source x)) hy
    _ = _ := by rw [map_add, map_add, hz1, hz3, zero_add, add_zero]

def copyMap (B : SymmetricMass rho) : IntertwiningMap a c :=
  (P.factor (P.massMap B)).choose

omit [FiniteDimensional ℂ A] in
theorem mass_factor (B : SymmetricMass rho) :
    P.massMap B = externalMap (IntertwiningMap.id r) (P.copyMap B) :=
  (P.factor (P.massMap B)).choose_spec

/-- Actual species realization derived for every symmetric invariant B. -/
def species (B : SymmetricMass rho) : Species (s := a) (t := c) r B where
  map := P.copyMap B
  embed := P.source
  injective := P.coordinates.symm.toLinearEquiv.injective.comp (fun x y he =>
    congrArg Prod.fst he)
  dualField := P.dualField
  mass_square := by rw [P.mass_column B, P.mass_factor B]

end Presentation
end

section Models
open Representation StandardSMGaugeTensor

variable {H F Aq Cq Au Cu Ae Ce Zq Zu Ze : Type*} [Group H]
  [AddCommGroup F] [Module ℂ F]
  [AddCommGroup Aq] [Module ℂ Aq] [FiniteDimensional ℂ Aq]
  [AddCommGroup Cq] [Module ℂ Cq] [FiniteDimensional ℂ Cq]
  [AddCommGroup Au] [Module ℂ Au] [FiniteDimensional ℂ Au]
  [AddCommGroup Cu] [Module ℂ Cu] [FiniteDimensional ℂ Cu]
  [AddCommGroup Ae] [Module ℂ Ae] [FiniteDimensional ℂ Ae]
  [AddCommGroup Ce] [Module ℂ Ce] [FiniteDimensional ℂ Ce]
  [AddCommGroup Zq] [Module ℂ Zq]
  [AddCommGroup Zu] [Module ℂ Zu]
  [AddCommGroup Ze] [Module ℂ Ze]
  (aq : Representation ℂ H Aq) (cq : Representation ℂ H Cq)
  (au : Representation ℂ H Au) (cu : Representation ℂ H Cu)
  (ae : Representation ℂ H Ae) (ce : Representation ℂ H Ce)
  (zq : Representation ℂ (GaugeGroup × H) Zq)
  (zu : Representation ℂ (GaugeGroup × H) Zu)
  (ze : Representation ℂ (GaugeGroup × H) Ze)
  (rho : Representation ℂ (GaugeGroup × H) F)

/-- A fixed original field/action model: all mass squares are derived from
mass-independent presentations, separately for the three selected species. -/
noncomputable def modelOfPresentations
    (Pq : Presentation quark aq cq zq rho)
    (Pu : Presentation upRight.dual au cu zu rho)
    (Pe : Presentation electronRight.dual ae ce ze rho) :
    PhysicalSpeciesCopySurplus.Model aq cq au cu ae ce rho where
  realize B := ⟨Pq.species B, Pu.species B, Pe.species B⟩

end Models
end GUT.SpeciesSectorPresentation
