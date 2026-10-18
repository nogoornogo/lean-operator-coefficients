import Math.RepresentationTheory.SU2WeightsDetermine
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Group a finite list of SU2 strings by its bounded degree. This is a
complete equivariant regrouping with arbitrary dependent retained modules,
including repeated degrees. No zero-padding or irreducible matching occurs. -/
namespace Math.SU2GroupStrings
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars
open scoped TensorProduct
variable {K J : Type*} [Group K] [Fintype J]
  {U : J → Type*} [∀ j, AddCommGroup (U j)] [∀ j, Module ℂ (U j)]
  (s : ∀ j, Representation ℂ K (U j)) (m : J → ℕ) (N : ℕ) (hm : ∀ j, m j≤N)
local instance : DecidableEq J := Classical.decEq _
@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n Doublet) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

def label (j : J) : Fin (N+1) := ⟨m j, Nat.lt_succ_of_le (hm j)⟩
abbrev Fiber (k : Fin (N+1)) := {j : J // label m N hm j=k}
local instance (k : Fin (N+1)) : Fintype (Fiber m N hm k) := Fintype.ofFinite _
abbrev grouped (k : Fin (N+1)) := FiniteBlockHom.action
  (fun j : Fiber m N hm k => s j.val)

def spinCast {a b : ℕ} (h : a=b) :
    Representation.Equiv (doublet.symmetricPower a) (doublet.symmetricPower b) := h ▸ .refl _

def distribute (k : Fin (N+1)) : Representation.Equiv
    (external (doublet.symmetricPower k.val) (grouped s m N hm k))
    (FiniteBlockHom.action (fun j : Fiber m N hm k =>
      external (doublet.symmetricPower k.val) (s j.val))) where
  toLinearEquiv := TensorProduct.piRight ℂ ℂ (Sym[ℂ]^k.val Doublet)
    (fun j : Fiber m N hm k => U j.val)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    funext j
    rfl

def matchingPiece (k : Fin (N+1)) (j : Fiber m N hm k) : Representation.Equiv
    (external (doublet.symmetricPower k.val) (s j.val))
    (SU2StringSliceSum.piece s m j.val) where
  toLinearEquiv := TensorProduct.congr
    (spinCast (congrArg Fin.val j.property).symm).toLinearEquiv (.refl ℂ _)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[ℂ] s j.val g.2 y)
      ((spinCast (congrArg Fin.val j.property).symm).isIntertwining _ _ g.1 x)

def flatten : Representation.Equiv
    (FiniteBlockHom.action (fun k : Fin (N+1) => FiniteBlockHom.action
      (fun j : Fiber m N hm k => SU2StringSliceSum.piece s m j.val)))
    (SU2StringSliceSum.source s m) where
  toLinearEquiv :=
    { toFun x j := x (label m N hm j) ⟨j,rfl⟩
      invFun x _ j := x j.val
      left_inv x := by
        funext k j
        rcases j with ⟨j,hj⟩
        subst k
        rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

/-- The original labelled string family, including repeated spin labels,
is the complete bounded isotypic sum of its grouped retained modules. -/
def equivalence : Representation.Equiv
    (SU2ConsecutiveSlices.total N (grouped s m N hm)) (SU2StringSliceSum.source s m) :=
  (FiniteExternalProducts.along (distribute s m N hm)).trans
    ((FiniteExternalProducts.along (fun k =>
      FiniteExternalProducts.along (matchingPiece s m N hm k))).trans
      (flatten s m N hm))

variable [TopologicalSpace K] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ (WeakDoubletScalars.Group × K) V)
  (hr : ContinuousRepresentationScope.IsJointlyContinuous rho)
  (hb : BoundedTorusWeights.Bounded (ProductFactorization.firstRestriction rho)
    TauCeti.SU2.torusHom N)

/-- Reconstruct an arbitrary finite labelled positive string family from
actual weight-space comparisons. Labels may repeat and degrees may be absent. -/
def reconstruct
    (h : ∀ k : ℤ, 0≤k → k≤(N : ℤ)+2 → Representation.Equiv
      (TorusWeightSlice.action rho TauCeti.SU2.torusHom k)
      (TorusWeightSlice.action (SU2StringSliceSum.source s m) TauCeti.SU2.torusHom k)) :
    Representation.Equiv rho (SU2StringSliceSum.source s m) :=
  (SU2WeightsDetermine.equivalence rho N hr hb (grouped s m N hm)
    (fun k hlo hhi => (h k hlo hhi).trans
      (TorusWeightSlice.transport (SU2StringSliceSum.source s m) TauCeti.SU2.torusHom
        (equivalence s m N hm).symm k))).trans (equivalence s m N hm)

end
end Math.SU2GroupStrings
