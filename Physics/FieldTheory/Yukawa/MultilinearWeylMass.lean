import Physics.FieldTheory.Yukawa.WeylMassFamily
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Finite multilinear sources for symmetric masses

The coefficient is complex multilinear in independent scalar slots and complex
bilinear in the fermions. Real-linear slot maps allow repeated fields, projections
from several multiplets, and conjugate fields. Thus the resulting scalar
dependence is real polynomial in finite dimensions, not necessarily holomorphic.
Equivariance is required of the coefficient and the slots, not of the final mass.
-/

set_option autoImplicit false

namespace GUT.WeylMassFamily

open InvariantWeylMass

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

namespace EquivariantFamily

noncomputable def sum {J : Type*} [Fintype J] (Y : J → EquivariantFamily rhoS rhoV) :
    EquivariantFamily rhoS rhoV where
  toFun s := ∑ j, (Y j).toFun s
  symmetric s := ⟨fun x y => by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => ((Y j).symmetric s).eq x y⟩
  invariant g s x y := by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => (Y j).invariant g s x y

@[simp] theorem sum_apply {J : Type*} [Fintype J]
    (Y : J → EquivariantFamily rhoS rhoV) (s : S) (x y : V) :
    (sum Y).toFun s x y = ∑ j, (Y j).toFun s x y := by
  simp [sum]

theorem sum_zero {J : Type*} [Fintype J] (Y : J → EquivariantFamily rhoS rhoV)
    (h : ∀ j, (Y j).toFun 0 = 0) : (sum Y).toFun 0 = 0 := by
  simp [sum, h]

end EquivariantFamily

variable {ι : Type*} {M : ι → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

structure MultilinearCoupling [Fintype ι] (rhoM : ∀ i, Representation ℂ G (M i))
    (rhoV : Representation ℂ G V) where
  coefficient : MultilinearMap ℂ M (LinearMap.BilinForm ℂ V)
  symmetric : ∀ m, (coefficient m).IsSymm
  invariant : ∀ g m x y,
    coefficient (fun i => rhoM i g (m i)) (rhoV g x) (rhoV g y) = coefficient m x y

namespace MultilinearCoupling

variable [Fintype ι]
variable {rhoM : ∀ i, Representation ℂ G (M i)}
variable [Module ℝ S] [∀ i, Module ℝ (M i)]

def toFamily (C : MultilinearCoupling rhoM rhoV) (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) :
    EquivariantFamily rhoS rhoV where
  toFun s := C.coefficient (fun i => slots i s)
  symmetric s := C.symmetric _
  invariant g s x y := by
    simp only [hslots]
    exact C.invariant g _ x y

@[simp] theorem toFamily_apply (C : MultilinearCoupling rhoM rhoV)
    (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) (s : S) :
    (C.toFamily slots hslots).toFun s = C.coefficient (fun i => slots i s) := rfl

theorem toFamily_zero [Nonempty ι] (C : MultilinearCoupling rhoM rhoV)
    (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) :
    (C.toFamily slots hslots).toFun 0 = 0 := by
  exact C.coefficient.map_coord_zero (Classical.arbitrary ι) (map_zero _)

/-- With the usual compatible real/complex actions, the source is the
diagonal of an actual real multilinear map, including conjugate slots. -/
def realCoefficient [∀ i, IsScalarTower ℝ ℂ (M i)]
    (C : MultilinearCoupling rhoM rhoV) (slots : ∀ i, S →ₗ[ℝ] M i) :
    MultilinearMap ℝ (fun _ : ι => S) (LinearMap.BilinForm ℂ V) :=
  (C.coefficient.restrictScalars ℝ).compLinearMap slots

theorem toFamily_realDiagonal [∀ i, IsScalarTower ℝ ℂ (M i)]
    (C : MultilinearCoupling rhoM rhoV) (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) (s : S) :
    (C.toFamily slots hslots).toFun s = C.realCoefficient slots (fun _ => s) := rfl

theorem toFamily_real_homogeneous [∀ i, IsScalarTower ℝ ℂ (M i)]
    (C : MultilinearCoupling rhoM rhoV) (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) (r : ℝ) (s : S) :
    (C.toFamily slots hslots).toFun (r • s) =
      r ^ Fintype.card ι • (C.toFamily slots hslots).toFun s := by
  rw [toFamily_realDiagonal, toFamily_realDiagonal]
  rw [(C.realCoefficient slots).map_smul_univ]
  simp

/-- Complex-linear slots are a special case of the real-linear interface. -/
def linearSlot {T : Type*} [AddCommGroup T] [Module ℂ T] [Module ℝ T]
    [IsScalarTower ℝ ℂ S] [IsScalarTower ℝ ℂ T] (f : S →ₗ[ℂ] T) : S →ₗ[ℝ] T :=
  f.restrictScalars ℝ

/-- Conjugation is real-linear, not complex-linear. Its equivariance must still
be checked against the chosen source and slot representations. -/
def conjugateSlot : ℂ →ₗ[ℝ] ℂ := Complex.conjAe.toLinearMap

@[simp] theorem conjugateSlot_apply (z : ℂ) : conjugateSlot z = star z := rfl

/-- Degree zero, with no scalar inputs. -/
def constant (rhoS : Representation ℂ G S) (B : SymmetricMass rhoV) :
    MultilinearCoupling (fun _ : Fin 0 => rhoS) rhoV where
  coefficient := MultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => S) B.form
  symmetric _ := B.symmetric
  invariant g _ := B.invariant g

theorem constant_toFamily (B : SymmetricMass rhoV) :
    (constant rhoS B).toFamily (fun _ => LinearMap.id)
      (fun _ _ _ => rfl) = EquivariantFamily.const (rhoS := rhoS) B := rfl

/-- Degree one recovers the old complex-linear coefficient without importing
the legacy physical source modules. -/
def ofLinear (L : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (hsym : ∀ s, (L s).IsSymm)
    (hinv : ∀ g s x y, L (rhoS g s) (rhoV g x) (rhoV g y) = L s x y) :
    MultilinearCoupling (fun _ : Fin 1 => rhoS) rhoV where
  coefficient := MultilinearMap.ofSubsingleton ℂ S (LinearMap.BilinForm ℂ V) 0 L
  symmetric m := hsym (m 0)
  invariant g m := hinv g (m 0)

@[simp] theorem ofLinear_toFamily (L : S →ₗ[ℂ] LinearMap.BilinForm ℂ V)
    (hsym : ∀ s, (L s).IsSymm)
    (hinv : ∀ g s x y, L (rhoS g s) (rhoV g x) (rhoV g y) = L s x y) (s : S) :
    ((ofLinear L hsym hinv).toFamily (fun _ => LinearMap.id)
      (fun _ _ _ => rfl)).toFun s = L s := rfl

end MultilinearCoupling
end GUT.WeylMassFamily
