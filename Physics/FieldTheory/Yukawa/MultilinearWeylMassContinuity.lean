import Physics.FieldTheory.Yukawa.MultilinearWeylMass
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic

/-! Finite coordinate expansions and joint continuity of the constructed
scalar/fermion coupling. No topology on algebraic bilinear-map spaces is chosen. -/

set_option autoImplicit false

namespace GUT.WeylMassFamily

open Module

section Coordinates

variable {ι : Type*} [Fintype ι] {M : ι → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
variable {N : Type*} [AddCommGroup N] [Module ℂ N]

open scoped Classical in
theorem multilinear_basis_expansion {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (b : ∀ i, Basis (κ i) ℂ (M i)) (C : MultilinearMap ℂ M N) (m : ∀ i, M i) :
    C m = ∑ p : ∀ i, κ i, (∏ i, (b i).repr (m i) (p i)) • C (fun i => b i (p i)) := by
  classical
  conv_lhs => rw [show m = (fun i => ∑ j, (b i).repr (m i) j • b i j) from
    funext fun i => ((b i).sum_repr (m i)).symm]
  rw [C.map_sum]
  simp only [C.map_smul_univ]

end Coordinates

section Continuity

variable {ι : Type*} [Fintype ι] {M : ι → Type*}
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℂ (M i)]
variable [∀ i, FiniteDimensional ℂ (M i)]

theorem continuous_multilinear_scalar (C : MultilinearMap ℂ M ℂ) : Continuous C := by
  classical
  let b := fun i => Module.finBasis ℂ (M i)
  have h := fun m => multilinear_basis_expansion b C m
  change Continuous (fun m => C m)
  rw [show (fun m => C m) = (fun m =>
    ∑ p : ∀ i, Fin (Module.finrank ℂ (M i)),
      (∏ i, (b i).repr (m i) (p i)) • C (fun i => b i (p i))) from funext h]
  apply continuous_finsetSum
  intro p _
  simp only [smul_eq_mul]
  exact (continuous_finsetProd _ fun i _ =>
    ((b i).coord (p i)).continuous_of_finiteDimensional.comp (continuous_apply i)).mul
    continuous_const

end Continuity

section Family

variable {G S V : Type*} [Group G]
variable [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedSpace ℝ S]
variable [FiniteDimensional ℝ S]
variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}
variable {ι : Type*} [Fintype ι] {M : ι → Type*}
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℂ (M i)]
variable [∀ i, NormedSpace ℝ (M i)] [∀ i, FiniteDimensional ℂ (M i)]
variable {rhoM : ∀ i, Representation ℂ G (M i)}

omit [NormedSpace ℂ S] [FiniteDimensional ℂ V] in
theorem MultilinearCoupling.continuous_coefficient (C : MultilinearCoupling rhoM rhoV)
    (slots : ∀ i, S →ₗ[ℝ] M i) (x y : V) :
    Continuous (fun s => C.coefficient (fun i => slots i s) x y) := by
  let ev : LinearMap.BilinForm ℂ V →ₗ[ℂ] ℂ :=
    { toFun := fun B => B x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (continuous_multilinear_scalar (ev.compMultilinearMap C.coefficient)).comp
    (continuous_pi fun i => (slots i).continuous_of_finiteDimensional)

/-- Joint continuity includes the fermions, not just fixed-basis coefficients. -/
theorem MultilinearCoupling.continuous_toFamily (C : MultilinearCoupling rhoM rhoV)
    (slots : ∀ i, S →ₗ[ℝ] M i)
    (hslots : ∀ g s i, slots i (rhoS g s) = rhoM i g (slots i s)) :
    Continuous (fun p : S × V × V => (C.toFamily slots hslots).toFun p.1 p.2.1 p.2.2) := by
  classical
  let b := Module.finBasis ℂ V
  have expand (B : LinearMap.BilinForm ℂ V) (x y : V) :
      B x y = ∑ i, ∑ j, b.repr x i * (b.repr y j * B (b i) (b j)) := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm]
  rw [show (fun p : S × V × V => (C.toFamily slots hslots).toFun p.1 p.2.1 p.2.2) =
    (fun p : S × V × V => ∑ i, ∑ j,
      b.repr p.2.1 i * (b.repr p.2.2 j * (C.toFamily slots hslots).toFun p.1 (b i) (b j))) from
    funext fun p => expand _ _ _]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((b.coord i).continuous_of_finiteDimensional.comp (continuous_fst.comp continuous_snd)).mul
    (((b.coord j).continuous_of_finiteDimensional.comp (continuous_snd.comp continuous_snd)).mul
      ((C.continuous_coefficient slots (b i) (b j)).comp continuous_fst))

end Family

section Sum

variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V] [TopologicalSpace S] [TopologicalSpace V]
variable {rhoS : Representation ℂ G S} {rhoV : Representation ℂ G V}

theorem EquivariantFamily.continuous_sum {J : Type*} [Fintype J]
    (Y : J → EquivariantFamily rhoS rhoV)
    (hY : ∀ j, Continuous (fun p : S × V × V => (Y j).toFun p.1 p.2.1 p.2.2)) :
    Continuous (fun p : S × V × V => (sum Y).toFun p.1 p.2.1 p.2.2) := by
  simp only [sum_apply]
  exact continuous_finsetSum _ fun j _ => hY j

end Sum
end GUT.WeylMassFamily
