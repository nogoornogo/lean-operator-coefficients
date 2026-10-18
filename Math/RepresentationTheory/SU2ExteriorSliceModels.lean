import Math.RepresentationTheory.SU2ExteriorWeightSlice
import Math.RepresentationTheory.SU2WeightsDetermine
import Math.RepresentationTheory.SU2GroupStrings
import Math.RepresentationTheory.BasisActionContinuity
import Math.RepresentationTheory.ExteriorContinuity
import Math.RepresentationTheory.BalancedExteriorWeights

/-! Continuous finite Hilbert copies of actual exterior-doublet sources,
with constructed torus bounds and the proved exterior weight comparisons.
No branching or multiplicity premise is introduced by the copy. -/
namespace Math.SU2ExteriorSliceModels
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars
open FiniteBasisHilbertization ContinuousUnitaryConstructions BoundedTorusWeights
open scoped TensorProduct
variable {K A I : Type*} [Group K] [TopologicalSpace K]
  [AddCommGroup A] [Module ℂ A] [Fintype I]
  (s : Representation ℂ K A) (b : Module.Basis I ℂ A)
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] A) := inferInstance
local instance : LinearOrder (Fin 2 × I) :=
  LinearOrder.lift' (Fintype.equivFin (Fin 2 × I)) (Fintype.equivFin _).injective

abbrev field := external doublet s
def fieldBasis := (Pi.basisFun ℂ (Fin 2)).tensorProduct b
abbrev fieldCopy := basisCopyRepresentation (fieldBasis b) (field s)
abbrev fieldEquiv := basisCopyRepresentationEquiv (fieldBasis b) (field s)

theorem doublet_coefficients : BasisActionContinuity.Coefficients
    (Pi.basisFun ℂ (Fin 2)) doublet := by
  intro i j
  have hc : Continuous (fun g : WeakDoubletScalars.Group =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) j i) :=
    (show Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m j i) from
      (continuous_apply i).comp (continuous_apply j)).comp
        (show Continuous (Subtype.val : WeakDoubletScalars.Group → Matrix (Fin 2) (Fin 2) ℂ)
          from continuous_subtype_val)
  simpa [doublet, TauCeti.stdRep_apply_apply, Pi.basisFun_apply] using hc

omit [Fintype I] in
theorem field_coefficients (hs : BasisActionContinuity.Coefficients b s) :
    BasisActionContinuity.Coefficients (fieldBasis b) (field s) :=
  BasisActionContinuity.tensor (Pi.basisFun ℂ (Fin 2)) b
    (doublet.comp (MonoidHom.fst WeakDoubletScalars.Group K))
    (s.comp (MonoidHom.snd WeakDoubletScalars.Group K))
    (BasisActionContinuity.comp (Pi.basisFun ℂ (Fin 2)) doublet doublet_coefficients
      (MonoidHom.fst WeakDoubletScalars.Group K) continuous_fst)
    (BasisActionContinuity.comp b s hs
      (MonoidHom.snd WeakDoubletScalars.Group K) continuous_snd)

theorem doublet_basis_eigen (i : Fin 2) (z : Circle) :
    doublet (TauCeti.SU2.torusHom z) (Pi.single i 1)=
      (z : ℂ)^(BinaryScalarExteriorSlice.weights i) • Pi.single i 1 := by
  funext j
  rw [SU2DoubletTorusSplit.doublet_torus]
  by_cases hji : j=i
  · subst j; simp
  · simp [Pi.single_eq_of_ne hji]

omit [TopologicalSpace K] [Fintype I] in
theorem field_basis_eigen (i : Fin 2 × I) :
    Eigen (ProductFactorization.firstRestriction (field s)) TauCeti.SU2.torusHom
      (BinaryScalarExteriorSlice.weights i.1) (fieldBasis b i) := by
  intro z
  rw [fieldBasis, Module.Basis.tensorProduct_apply]
  change doublet (TauCeti.SU2.torusHom z) ((Pi.basisFun ℂ (Fin 2)) i.1) ⊗ₜ[ℂ]
      s 1 (b i.2)=(z : ℂ)^(BinaryScalarExteriorSlice.weights i.1) •
        (((Pi.basisFun ℂ (Fin 2)) i.1) ⊗ₜ[ℂ] b i.2)
  simp only [Pi.basisFun_apply, doublet_basis_eigen, map_one, Module.End.one_apply]
  rfl

omit [TopologicalSpace K] in
include b in
theorem exterior_bound (n : ℕ) : Bounded
    ((ProductFactorization.firstRestriction (field s)).exteriorPower n)
    TauCeti.SU2.torusHom (min n (Fintype.card (Fin 2 × I)-n)) := by
  apply BalancedExteriorWeights.bounded _ _ (fieldBasis b)
    (fun i => BinaryScalarExteriorSlice.weights i.1) (field_basis_eigen s b)
  · intro i
    rcases i with ⟨i,j⟩
    fin_cases i <;> simp [BinaryScalarExteriorSlice.weights]
  · simp [Fintype.sum_prod_type, Fin.sum_univ_two, BinaryScalarExteriorSlice.weights]

def exteriorBasis (n : ℕ) := (fieldBasis b).exteriorPower n
abbrev Carrier (n : ℕ) := Copy (exteriorBasis b n)
abbrev action (n : ℕ) := basisCopyRepresentation (exteriorBasis b n) ((field s).exteriorPower n)
abbrev equivalence (n : ℕ) :=
  basisCopyRepresentationEquiv (exteriorBasis b n) ((field s).exteriorPower n)

omit [TopologicalSpace K] in
theorem model_bound (n : ℕ) : Bounded
    (ProductFactorization.firstRestriction (action s b n)) TauCeti.SU2.torusHom
    (min n (Fintype.card (Fin 2 × I)-n)) :=
  BoundedTorusWeights.bounded_of_surjective
    ((ProductFactorization.firstRestriction (field s)).exteriorPower n)
    TauCeti.SU2.torusHom (ProductFactorization.firstRestriction (action s b n))
    ((SplitRepresentationProjection.restrictEquiv (equivalence s b n)
      (MonoidHom.inl WeakDoubletScalars.Group K)).toIntertwiningMap)
    (equivalence s b n).surjective _ (exterior_bound s b n)

theorem continuous (hc : BasisActionContinuity.Coefficients (fieldBasis b) (field s)) (n : ℕ) :
    ContinuousRepresentationScope.IsJointlyContinuous (action s b n) :=
  ExteriorContinuity.representation_continuous (fieldCopy s b)
    (BasisActionContinuity.copy_continuous (fieldBasis b) (field s) hc).orbit n
    (action s b n) (((fieldEquiv s b).symm.exteriorPower n).trans (equivalence s b n))

@[reducible] local instance (p q : ℕ) : AddCommGroup
    ((⋀[ℂ]^p A) ⊗[ℂ] (⋀[ℂ]^q A)) := Module.addCommMonoidToAddCommGroup ℂ

/-- The actual copied source has the same retained-action weight product;
the analytic copy changes no support condition. -/
def weightEquivalence (p q : ℕ) : Representation.Equiv
    (TorusWeightSlice.action (action s b (p+q)) TauCeti.SU2.torusHom ((p : ℤ)-q))
    ((s.exteriorPower p).tprod (s.exteriorPower q)) :=
  (TorusWeightSlice.transport (action s b (p+q)) TauCeti.SU2.torusHom
    (equivalence s b (p+q)).symm _).trans (SU2ExteriorWeightSlice.equivalence s p q)

omit [TopologicalSpace K] in
theorem outside_string (n : ℕ) (k : ℤ) (hk : ¬SU2WeightSlice.InString n k)
    (x : TorusWeightSlice.Space (action s b n) TauCeti.SU2.torusHom k) : x=0 := by
  let e := TorusWeightSlice.transport (action s b n) TauCeti.SU2.torusHom
    (equivalence s b n).symm k
  apply e.injective
  exact (SU2ExteriorWeightSlice.outside_string s n k hk (e x)).trans
    (map_zero e.toIntertwiningMap.toLinearMap).symm

abbrev bound (n : ℕ) := min n (Fintype.card (Fin 2 × I)-n)

variable {n : ℕ}
  {U : Fin (bound (I := I) n+1) → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  (candidate : ∀ i, Representation ℂ K (U i))
@[reducible] local instance (i : Fin (bound (I := I) n+1)) :
    AddCommGroup (Sym[ℂ]^i.val Doublet) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (i : Fin (bound (I := I) n+1)) :
    AddCommGroup ((Sym[ℂ]^i.val Doublet) ⊗[ℂ] U i) := inferInstance

/-- A proved family of actual slice comparisons reconstructs a full
exterior-source decomposition. Continuity and the source bound are proved
from finite basis coefficients and the doublet action. -/
def reconstruct (hs : BasisActionContinuity.Coefficients b s)
    (hw : ∀ k : ℤ, 0≤k → k≤(bound (I := I) n : ℤ)+2 →
      Representation.Equiv (TorusWeightSlice.action (action s b n) TauCeti.SU2.torusHom k)
        (TorusWeightSlice.action (SU2ConsecutiveSlices.total (bound (I := I) n) candidate)
          TauCeti.SU2.torusHom k)) :
    Representation.Equiv ((field s).exteriorPower n)
      (SU2ConsecutiveSlices.total (bound (I := I) n) candidate) :=
  (equivalence s b n).trans
    (SU2WeightsDetermine.equivalence (action s b n) (bound (I := I) n)
      (continuous s b (field_coefficients s b hs) n) (model_bound s b n) candidate hw)

end
end Math.SU2ExteriorSliceModels
