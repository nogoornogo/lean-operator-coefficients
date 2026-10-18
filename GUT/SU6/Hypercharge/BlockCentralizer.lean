import Math.RepresentationTheory.Decomposition.Schur
import GUT.SU6.Embeddings.LowDimensionalConcreteIrreps
import GUT.SU6.Hypercharge.HyperchargeCentralizer
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Trace

open Math

/-!
# The commutant of the standard three-block representation

This file supplies the Schur-theoretic front end of Claim hypercharge centralizer geometry.  It first proves
that an intertwiner between finite-dimensional irreducible representations of
different dimensions is zero.  It then computes the full commutant of a sum
of three pairwise dimension-distinct irreducibles and specializes the result
to the standard

`(3,1) + (1,2) + (1,1)`

representation of `SU(3) x SU(2)`.
-/

namespace GUT
namespace BlockCentralizer

open Math.BlockCentralizer

open CompactEmbeddingClassification
open LowDimensionalCenterActions
open LowDimensionalConcreteIrreps

noncomputable section

/-!
## General Schur lemmas
-/

variable {k G H : Type*} [Field k] [IsAlgClosed k]
variable [Monoid G] [Monoid H]
variable {V₁ V₂ V₃ : Type*}
variable [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
variable [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
variable [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]

/-!
## Transport of commutants
-/

/-- Conjugate a commuting endomorphism across an equivalence of
representations. -/
def transportCommutant
    (rho : Representation k G V₁) (sigma : Representation k G V₂)
    (e : Representation.Equiv rho sigma)
    (f : Representation.IntertwiningMap rho rho) :
    Representation.IntertwiningMap sigma sigma :=
  e.toIntertwiningMap.comp (f.comp e.symm.toIntertwiningMap)

omit [IsAlgClosed k] [FiniteDimensional k V₁] [FiniteDimensional k V₂] in
@[simp]
theorem transportCommutant_apply
    (rho : Representation k G V₁) (sigma : Representation k G V₂)
    (e : Representation.Equiv rho sigma)
    (f : Representation.IntertwiningMap rho rho) (x : V₂) :
    transportCommutant rho sigma e f x = e (f (e.symm x)) :=
  rfl

omit [IsAlgClosed k] [FiniteDimensional k V₁] [FiniteDimensional k V₂] in
/-- Conjugating a commuting endomorphism across a representation equivalence
preserves its trace. -/
theorem trace_transportCommutant
    (rho : Representation k G V₁) (sigma : Representation k G V₂)
    (e : Representation.Equiv rho sigma)
    (f : Representation.IntertwiningMap rho rho) :
    LinearMap.trace k V₂ (transportCommutant rho sigma e f).toLinearMap =
      LinearMap.trace k V₁ f.toLinearMap := by
  simpa [transportCommutant, LinearEquiv.conj_apply,
    LinearMap.comp_assoc, Representation.Equiv.toLinearMap_symm] using
      (LinearMap.trace_conj' f.toLinearMap e.toLinearEquiv)

omit [IsAlgClosed k] [FiniteDimensional k V₁] [FiniteDimensional k V₂] in
/-- Conjugating a commuting endomorphism across a representation equivalence
preserves its determinant. -/
theorem det_transportCommutant
    (rho : Representation k G V₁) (sigma : Representation k G V₂)
    (e : Representation.Equiv rho sigma)
    (f : Representation.IntertwiningMap rho rho) :
    LinearMap.det (transportCommutant rho sigma e f).toLinearMap =
      LinearMap.det f.toLinearMap := by
  simpa [transportCommutant, LinearEquiv.conj_apply,
    LinearMap.comp_assoc, Representation.Equiv.toLinearMap_symm] using
      (LinearMap.det_conj f.toLinearMap e.toLinearEquiv)

omit [IsAlgClosed k] [FiniteDimensional k V₁] [FiniteDimensional k V₂] in
/-- Conjugation across a representation equivalence is injective on the
commutant. -/
theorem transportCommutant_injective
    (rho : Representation k G V₁) (sigma : Representation k G V₂)
    (e : Representation.Equiv rho sigma) :
    Function.Injective (transportCommutant rho sigma e) := by
  intro f g h
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply e.injective
  have hApply := congrArg
    (fun q : Representation.IntertwiningMap sigma sigma => q (e x)) h
  simpa [transportCommutant_apply] using hApply

section ThreeBlocks

variable (rho₁ : Representation k G V₁)
variable (rho₂ : Representation k G V₂)
variable (rho₃ : Representation k G V₃)
variable [Representation.IsIrreducible rho₁]
variable [Representation.IsIrreducible rho₂]
variable [Representation.IsIrreducible rho₃]

/-- The full commutant of three pairwise dimension-distinct irreducible
representations is block-scalar. -/
theorem threeBlock_commutant_is_blockScalar
    (h₁₂ : Module.finrank k V₁ ≠ Module.finrank k V₂)
    (h₁₃ : Module.finrank k V₁ ≠ Module.finrank k V₃)
    (h₂₃ : Module.finrank k V₂ ≠ Module.finrank k V₃)
    (f : Representation.IntertwiningMap
      (rho₁.prod (rho₂.prod rho₃)) (rho₁.prod (rho₂.prod rho₃))) :
    ∃ c₁ c₂ c₃ : k, ∀ x₁ x₂ x₃,
      f (x₁, (x₂, x₃)) = (c₁ • x₁, (c₂ • x₂, c₃ • x₃)) := by
  let rho₂₃ := rho₂.prod rho₃
  let rho := rho₁.prod rho₂₃
  let i₁ : Representation.IntertwiningMap rho₁ rho :=
    Representation.IntertwiningMap.inl k rho₁ rho₂₃
  let i₂ : Representation.IntertwiningMap rho₂ rho :=
    (Representation.IntertwiningMap.inr k rho₁ rho₂₃).comp
      (Representation.IntertwiningMap.inl k rho₂ rho₃)
  let i₃ : Representation.IntertwiningMap rho₃ rho :=
    (Representation.IntertwiningMap.inr k rho₁ rho₂₃).comp
      (Representation.IntertwiningMap.inr k rho₂ rho₃)
  let p₁ : Representation.IntertwiningMap rho rho₁ :=
    Representation.IntertwiningMap.fst k rho₁ rho₂₃
  let p₂ : Representation.IntertwiningMap rho rho₂ :=
    (Representation.IntertwiningMap.fst k rho₂ rho₃).comp
      (Representation.IntertwiningMap.snd k rho₁ rho₂₃)
  let p₃ : Representation.IntertwiningMap rho rho₃ :=
    (Representation.IntertwiningMap.snd k rho₂ rho₃).comp
      (Representation.IntertwiningMap.snd k rho₁ rho₂₃)

  obtain ⟨c₁, h₁₁⟩ :=
    intertwiningMap_eq_smul_one_of_irreducible rho₁
      (p₁.comp (f.comp i₁))
  obtain ⟨c₂, h₂₂⟩ :=
    intertwiningMap_eq_smul_one_of_irreducible rho₂
      (p₂.comp (f.comp i₂))
  obtain ⟨c₃, h₃₃⟩ :=
    intertwiningMap_eq_smul_one_of_irreducible rho₃
      (p₃.comp (f.comp i₃))

  have h₁₂' : p₁.comp (f.comp i₂) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne (Ne.symm h₁₂) _
  have h₁₃' : p₁.comp (f.comp i₃) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne (Ne.symm h₁₃) _
  have h₂₁' : p₂.comp (f.comp i₁) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne h₁₂ _
  have h₂₃' : p₂.comp (f.comp i₃) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne (Ne.symm h₂₃) _
  have h₃₁' : p₃.comp (f.comp i₁) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne h₁₃ _
  have h₃₂' : p₃.comp (f.comp i₂) = 0 :=
    intertwiningMap_eq_zero_of_finrank_ne h₂₃ _

  refine ⟨c₁, c₂, c₃, ?_⟩
  intro x₁ x₂ x₃
  have hx : (x₁, (x₂, x₃)) = i₁ x₁ + i₂ x₂ + i₃ x₃ := by
    ext <;>
      simp [i₁, i₂, i₃, rho, rho₂₃,
        Representation.IntertwiningMap.inl,
        Representation.IntertwiningMap.inr,
        Representation.IntertwiningMap.prod]
  rw [hx, map_add, map_add]
  apply Prod.ext
  · have h₁₁x := congrArg
      (fun q : Representation.IntertwiningMap rho₁ rho₁ => q x₁) h₁₁
    have h₁₂x := congrArg
      (fun q : Representation.IntertwiningMap rho₂ rho₁ => q x₂) h₁₂'
    have h₁₃x := congrArg
      (fun q : Representation.IntertwiningMap rho₃ rho₁ => q x₃) h₁₃'
    simpa [p₁, rho, rho₂₃] using congrArg₂ (fun a b => a + b)
      (congrArg₂ (fun a b => a + b) h₁₁x h₁₂x) h₁₃x
  · apply Prod.ext
    · have h₂₁x := congrArg
        (fun q : Representation.IntertwiningMap rho₁ rho₂ => q x₁) h₂₁'
      have h₂₂x := congrArg
        (fun q : Representation.IntertwiningMap rho₂ rho₂ => q x₂) h₂₂
      have h₂₃x := congrArg
        (fun q : Representation.IntertwiningMap rho₃ rho₂ => q x₃) h₂₃'
      simpa [p₂, rho, rho₂₃] using congrArg₂ (fun a b => a + b)
        (congrArg₂ (fun a b => a + b) h₂₁x h₂₂x) h₂₃x
    · have h₃₁x := congrArg
        (fun q : Representation.IntertwiningMap rho₁ rho₃ => q x₁) h₃₁'
      have h₃₂x := congrArg
        (fun q : Representation.IntertwiningMap rho₂ rho₃ => q x₂) h₃₂'
      have h₃₃x := congrArg
        (fun q : Representation.IntertwiningMap rho₃ rho₃ => q x₃) h₃₃
      simpa [p₃, rho, rho₂₃] using congrArg₂ (fun a b => a + b)
        (congrArg₂ (fun a b => a + b) h₃₁x h₃₂x) h₃₃x

end ThreeBlocks

/-!
## The standard `SU(3) x SU(2)` blocks
-/

/-- The defining color triplet, with the weak factor acting trivially. -/
def colorBlock : Representation ℂ ProductGroup ColorStd :=
  su3Defining.comp (MonoidHom.fst SU3 SU2)

/-- The defining weak doublet, with the color factor acting trivially. -/
def weakBlock : Representation ℂ ProductGroup WeakStd :=
  su2Defining.comp (MonoidHom.snd SU3 SU2)

/-- The one-dimensional trivial block. -/
def singletBlock : Representation ℂ ProductGroup ℂ :=
  trivialLine ProductGroup

/-- The concrete standard `3+2+1` semisimple representation. -/
def standardBlockRepresentation :
    Representation ℂ ProductGroup (ColorStd × (WeakStd × ℂ)) :=
  colorBlock.prod (weakBlock.prod singletBlock)

/-- The vector space underlying the standard three-block representation. -/
abbrev StandardSpace := ColorStd × (WeakStd × ℂ)

instance colorBlock_isIrreducible :
    Representation.IsIrreducible colorBlock := by
  let _ : Representation.IsIrreducible su3Defining :=
    su3Defining_isIrreducible
  exact comp_isIrreducible_of_surjective su3Defining
    (MonoidHom.fst SU3 SU2) Prod.fst_surjective

instance weakBlock_isIrreducible :
    Representation.IsIrreducible weakBlock := by
  let _ : Representation.IsIrreducible su2Defining :=
    su2Defining_isIrreducible
  exact comp_isIrreducible_of_surjective su2Defining
    (MonoidHom.snd SU3 SU2) Prod.snd_surjective

instance singletBlock_isIrreducible :
    Representation.IsIrreducible singletBlock :=
  trivialLine_isIrreducible ProductGroup

/-- The linear endomorphism with scalar coefficients `c`, `w`, and `s` on the
three standard blocks. -/
def blockScalarLinearMap (c w s : ℂ) : StandardSpace →ₗ[ℂ] StandardSpace :=
  LinearMap.prodMap (c • LinearMap.id)
    (LinearMap.prodMap (w • LinearMap.id) (s • LinearMap.id))

@[simp]
theorem blockScalarLinearMap_apply (c w s : ℂ) (x : ColorStd)
    (y : WeakStd) (z : ℂ) :
    blockScalarLinearMap c w s (x, (y, z)) =
      (c • x, (w • y, s • z)) := by
  simp [blockScalarLinearMap]

/-- Every block-scalar endomorphism commutes with the standard semisimple
action. -/
def blockScalarIntertwiner (c w s : ℂ) :
    Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation where
  toLinearMap := blockScalarLinearMap c w s
  isIntertwining' g := by
    apply LinearMap.ext
    rintro ⟨x, ⟨y, z⟩⟩
    simp [standardBlockRepresentation, blockScalarLinearMap, singletBlock,
      trivialLine]

/-- The three block coefficients are uniquely detected by the resulting
intertwiner. -/
theorem blockScalarIntertwiner_eq_iff {c w s c' w' s' : ℂ} :
    blockScalarIntertwiner c w s = blockScalarIntertwiner c' w' s' ↔
      c = c' ∧ w = w' ∧ s = s' := by
  constructor
  · intro h
    have hc := congrArg
      (fun q : Representation.IntertwiningMap
          standardBlockRepresentation standardBlockRepresentation =>
        (q (Pi.basisFun ℂ (Fin 3) 0, (0, 0))).1 0) h
    have hw := congrArg
      (fun q : Representation.IntertwiningMap
          standardBlockRepresentation standardBlockRepresentation =>
        (q (0, (Pi.basisFun ℂ (Fin 2) 0, 0))).2.1 0) h
    have hs := congrArg
      (fun q : Representation.IntertwiningMap
          standardBlockRepresentation standardBlockRepresentation =>
        (q (0, (0, 1))).2.2) h
    simpa [blockScalarIntertwiner, blockScalarLinearMap,
      Pi.basisFun_apply] using And.intro hc (And.intro hw hs)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Every endomorphism commuting with the standard semisimple action is
scalar on each of the color, weak, and singlet blocks. -/
theorem standardBlock_commutant_is_blockScalar
    (f : Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation) :
    ∃ c w s : ℂ, ∀ x y z,
      f (x, (y, z)) = (c • x, (w • y, s • z)) := by
  apply threeBlock_commutant_is_blockScalar colorBlock weakBlock singletBlock
  · simp [ColorStd, WeakStd]
  · simp [ColorStd]
  · simp [WeakStd]

/-- Equality with the explicit block-scalar intertwiner, rather than only a
pointwise description. -/
theorem standardBlock_commutant_eq_blockScalarIntertwiner
    (f : Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation) :
    ∃ c w s : ℂ, f = blockScalarIntertwiner c w s := by
  obtain ⟨c, w, s, h⟩ := standardBlock_commutant_is_blockScalar f
  refine ⟨c, w, s, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨x, ⟨y, z⟩⟩
  exact h x y z

/-- The trace of a block-scalar endomorphism is the dimension-weighted sum of
its three coefficients. -/
theorem trace_blockScalarLinearMap (c w s : ℂ) :
    LinearMap.trace ℂ StandardSpace (blockScalarLinearMap c w s) =
      3 * c + 2 * w + s := by
  rw [blockScalarLinearMap, LinearMap.trace_prodMap',
    LinearMap.trace_prodMap']
  simp [ColorStd, WeakStd]
  ring

/-- A traceless endomorphism in the commutant has block coefficients satisfying
the `3+2+1` trace equation. -/
theorem traceless_standardBlock_commutant
    (f : Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation)
    (hTrace : LinearMap.trace ℂ StandardSpace f.toLinearMap = 0) :
    ∃ c w s : ℂ,
      f = blockScalarIntertwiner c w s ∧ 3 * c + 2 * w + s = 0 := by
  obtain ⟨c, w, s, hf⟩ :=
    standardBlock_commutant_eq_blockScalarIntertwiner f
  refine ⟨c, w, s, hf, ?_⟩
  rw [hf] at hTrace
  simpa [blockScalarIntertwiner, trace_blockScalarLinearMap] using hTrace

/-- The explicit complexified combination `a*Y5 + b*X` in the standard
commutant. -/
def standardExtraIntertwiner (a b : ℂ) :
    Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation :=
  blockScalarIntertwiner (-2 * a + b) (3 * a + b) (-5 * b)

/-- The two `Y5/X` coefficients are unique. -/
theorem standardExtraIntertwiner_injective :
    Function.Injective
      (fun p : ℂ × ℂ => standardExtraIntertwiner p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have hCoefficients := blockScalarIntertwiner_eq_iff.mp h
  rcases hCoefficients with ⟨hc, hw, _⟩
  have ha5 : 5 * a = 5 * a' := by
    calc
      5 * a = (3 * a + b) - (-2 * a + b) := by ring
      _ = (3 * a' + b') - (-2 * a' + b') := by rw [hw, hc]
      _ = 5 * a' := by ring
  have ha : a = a' := by
    calc
      a = (1 / 5 : ℂ) * (5 * a) := by ring
      _ = (1 / 5 : ℂ) * (5 * a') := by rw [ha5]
      _ = a' := by ring
  have hb : b = b' := by
    calc
      b = (-2 * a + b) + 2 * a := by ring
      _ = (-2 * a' + b') + 2 * a' := by rw [hc, ha]
      _ = b' := by ring
  exact Prod.ext ha hb

theorem standardExtraIntertwiner_trace_zero (a b : ℂ) :
    LinearMap.trace ℂ StandardSpace
      (standardExtraIntertwiner a b).toLinearMap = 0 := by
  rw [standardExtraIntertwiner, blockScalarIntertwiner,
    trace_blockScalarLinearMap]
  ring

/-- The full traceless commutant of the standard three-block representation
is spanned by the standard `Y5` and extra `X` directions. -/
theorem traceless_standardBlock_commutant_eq_standardExtra
    (f : Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation)
    (hTrace : LinearMap.trace ℂ StandardSpace f.toLinearMap = 0) :
    ∃ a b : ℂ, f = standardExtraIntertwiner a b := by
  obtain ⟨c, w, s, hf, hTraceless⟩ :=
    traceless_standardBlock_commutant f hTrace
  let a := (w - c) / 5
  let b := -s / 5
  have hc : -2 * a + b = c := by
    dsimp [a, b]
    calc
      -2 * ((w - c) / 5) + -s / 5 =
          c - (3 * c + 2 * w + s) / 5 := by ring
      _ = c := by rw [hTraceless]; simp
  have hw : 3 * a + b = w := by
    dsimp [a, b]
    calc
      3 * ((w - c) / 5) + -s / 5 =
          w - (3 * c + 2 * w + s) / 5 := by ring
      _ = w := by rw [hTraceless]; simp
  have hs : -5 * b = s := by
    dsimp [b]
    ring
  refine ⟨a, b, ?_⟩
  rw [hf, standardExtraIntertwiner, hc, hw, hs]

/-- Once a representation equivalence with the standard block model is
provided, every traceless element of the original commutant transports to a
unique `Y5/X` combination. -/
theorem traceless_commutant_eq_standardExtra_of_equiv
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ ProductGroup V)
    (e : Representation.Equiv rho standardBlockRepresentation)
    (f : Representation.IntertwiningMap rho rho)
    (hTrace : LinearMap.trace ℂ V f.toLinearMap = 0) :
    ∃ a b : ℂ,
      transportCommutant rho standardBlockRepresentation e f =
        standardExtraIntertwiner a b := by
  apply traceless_standardBlock_commutant_eq_standardExtra
  simpa only [trace_transportCommutant] using hTrace

/-- The traceless part of the complexified commutant. -/
def TracelessCommutant :=
  {f : Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation //
    LinearMap.trace ℂ StandardSpace f.toLinearMap = 0}

/-- Send the two `Y5/X` coefficients to the corresponding traceless
commutant element. -/
def standardExtraParameterization (p : ℂ × ℂ) : TracelessCommutant :=
  ⟨standardExtraIntertwiner p.1 p.2,
    standardExtraIntertwiner_trace_zero p.1 p.2⟩

theorem standardExtraParameterization_injective :
    Function.Injective standardExtraParameterization := by
  intro p q h
  apply standardExtraIntertwiner_injective
  exact congrArg Subtype.val h

theorem standardExtraParameterization_surjective :
    Function.Surjective standardExtraParameterization := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b, h⟩ :=
    traceless_standardBlock_commutant_eq_standardExtra f hf
  refine ⟨(a, b), ?_⟩
  apply Subtype.ext
  exact h.symm

/-- The traceless complexified commutant of the standard `3+2+1` action has
exactly the two coefficients multiplying `Y5` and `X`. -/
noncomputable def tracelessCommutantEquiv :
    (ℂ × ℂ) ≃ TracelessCommutant :=
  Equiv.ofBijective standardExtraParameterization
    ⟨standardExtraParameterization_injective,
      standardExtraParameterization_surjective⟩

/-- Rational hypercharge coefficients define a traceless element of the
complexified standard commutant. -/
def rationalGeneratorIntertwiner
    (Y : HyperchargeCentralizer.Generator) :
    Representation.IntertwiningMap
      standardBlockRepresentation standardBlockRepresentation :=
  blockScalarIntertwiner Y.color Y.weak Y.singlet

theorem rationalGeneratorIntertwiner_trace_zero
    (Y : HyperchargeCentralizer.Generator) :
    LinearMap.trace ℂ StandardSpace
      (rationalGeneratorIntertwiner Y).toLinearMap = 0 := by
  rw [rationalGeneratorIntertwiner, blockScalarIntertwiner,
    trace_blockScalarLinearMap]
  exact_mod_cast Y.traceless

end

end BlockCentralizer
end GUT
