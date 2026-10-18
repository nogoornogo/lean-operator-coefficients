import Math.RepresentationTheory.CyclicCharge
import Math.RepresentationTheory.InvariantFunctionalCoordinates
import Math.LinearAlgebra.SelectionCriteria
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.LinearAlgebra.SymmetricPower.Basis
import Math.RepresentationTheory.TensorSquareMultilinear

/-! Faithful cyclic weight coordinates, including empty and unequal carriers. -/
namespace Math.CyclicWeightCoordinates
set_option autoImplicit false
noncomputable section
open Representation SelectionCriteria
variable {N : ℕ} [NeZero N] {I : Type*}

def diagonal (q : I → ZMod N) : Representation ℂ (CyclicCharge.Group N) (I → ℂ) where
  toFun g :=
    { toFun := fun x i => ZMod.stdAddChar (q i * Multiplicative.toAdd g) * x i
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro z x; funext i; simp [smul_eq_mul, mul_left_comm] }
  map_one' := by ext x i; simp
  map_mul' g h := by ext x i; simp [mul_add, AddChar.map_add_eq_mul, mul_assoc]

@[simp] theorem diagonal_apply (q : I → ZMod N) (g) (x : I → ℂ) (i : I) :
    diagonal q g x i = ZMod.stdAddChar (q i * Multiplicative.toAdd g) * x i := rfl

theorem diagonal_basis [Finite I] [DecidableEq I] (q : I → ZMod N) (g) (i : I) :
    diagonal q g (Pi.basisFun ℂ I i) =
      ZMod.stdAddChar (q i * Multiplicative.toAdd g) • Pi.basisFun ℂ I i := by
  ext j
  by_cases h : j=i
  · subst j; simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

def supported (q : I → ZMod N) : Submodule ℂ (I → ℂ) where
  carrier := {c | ∀ i, q i ≠ 0 → c i = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intro z a ha i hi; simp [ha i hi]

def supportedEquiv (q : I → ZMod N) : supported q ≃ₗ[ℂ] ({i // q i=0} → ℂ) where
  toFun c i := c.val i.val
  invFun c := ⟨fun i => if h : q i=0 then c ⟨i,h⟩ else 0, by
    intro i hi; simp [hi]⟩
  left_inv c := by
    apply Subtype.ext; funext i
    by_cases h : q i=0
    · simp [h]
    · simp [h, c.property i h]
  right_inv c := by funext i; simp [i.property]
  map_add' a b := by rfl
  map_smul' z a := by rfl

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
  (r : Representation ℂ (CyclicCharge.Group N) V) (b : Module.Basis I ℂ V)
  (q : I → ZMod N)

def IsWeightBasis : Prop := ∀ g i,
  r g (b i) = ZMod.stdAddChar (q i * Multiplicative.toAdd g) • b i

theorem invariant_iff (h : IsWeightBasis r b q) (c : I → ℂ) :
    c ∈ InvariantFunctionalCoordinates.space r b ↔ c ∈ supported q := by
  constructor
  · intro hc i hi
    by_contra hn
    have hz : q i=0 := (CyclicCharge.neutral_iff (q i)).mp (by
      intro g
      have he := DFunLike.congr_fun (hc g) (b i)
      simp only [LinearMap.comp_apply, h g i, map_smul,
        Module.Basis.constr_basis, smul_eq_mul] at he
      exact mul_right_cancel₀ hn (he.trans (one_mul _).symm))
    exact hi hz
  · intro hc g
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, h g i, map_smul, Module.Basis.constr_basis,
      smul_eq_mul]
    by_cases hi : q i=0
    · simp [hi]
    · simp [hc i hi]

def invariantEquiv (h : IsWeightBasis r b q) :
    IntertwiningMap r (trivial ℂ (CyclicCharge.Group N) ℂ) ≃ₗ[ℂ]
      ({i // q i=0} → ℂ) :=
  (InvariantFunctionalCoordinates.equiv r b).trans
    ((LinearEquiv.ofEq _ _ (Submodule.ext (invariant_iff r b q h))).trans
      (supportedEquiv q))

theorem finrank [Fintype I] (h : IsWeightBasis r b q) :
    Module.finrank ℂ (IntertwiningMap r (trivial ℂ (CyclicCharge.Group N) ℂ)) =
      Fintype.card {i // q i=0} := by
  rw [(invariantEquiv r b q h).finrank_eq]
  simp

theorem allowed_iff (h : IsWeightBasis r b q) :
    Allowed (IntertwiningMap r (trivial ℂ (CyclicCharge.Group N) ℂ)) ↔
      ∃ i, q i=0 := by
  rw [allowed_equiv (invariantEquiv r b q h)]
  constructor
  · rintro ⟨c,hc⟩
    by_contra hn
    apply hc; funext i
    exact False.elim (hn ⟨i.val,i.property⟩)
  · rintro ⟨i,hi⟩
    exact ⟨fun _ => 1, by intro hz; have he := congrFun hz ⟨i,hi⟩; simp at he⟩

theorem diagonal_weights [Finite I] [DecidableEq I] :
    IsWeightBasis (diagonal q) (Pi.basisFun ℂ I) q := diagonal_basis q

section Tensor
open scoped TensorProduct
variable {J W : Type*} [AddCommMonoid W] [Module ℂ W]
  (s : Representation ℂ (CyclicCharge.Group N) W) (c : Module.Basis J ℂ W)
  (t : J → ZMod N)

theorem tensor_weights (h : IsWeightBasis r b q) (k : IsWeightBasis s c t) :
    IsWeightBasis (r.tprod s) (b.tensorProduct c) (fun ij => q ij.1+t ij.2) := by
  intro g ij
  rw [Module.Basis.tensorProduct_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    h g ij.1, k g ij.2, TensorProduct.smul_tmul_smul]
  simp [add_mul, AddChar.map_add_eq_mul]
end Tensor

def symmetricCharge (n : ℕ) (q : I → ZMod N) (s : Sym I n) : ZMod N :=
  ((s : Multiset I).map q).sum

theorem symmetric_weights (n : ℕ) (h : IsWeightBasis r b q) :
    IsWeightBasis (r.symmetricPower n) (b.symmetricPower n) (symmetricCharge n q) := by
  intro g s
  change SymmetricPower.map (r g) (b.symmetricPower n s) = _
  rw [SymmetricPower.map_basis_symmetricPower_of_apply_basis b (r g)
    (fun i => ZMod.stdAddChar (q i * Multiplicative.toAdd g)) (h g)]
  congr 1
  obtain ⟨f,rfl⟩ := TauCeti.Sym.ofFn_surjective s
  simp only [TauCeti.Sym.coe_ofFn, Multiset.map_coe, Multiset.prod_coe,
    Multiset.sum_coe, List.map_ofFn, List.prod_ofFn, List.sum_ofFn, symmetricCharge]
  rw [Finset.sum_mul]
  have hc (s : Finset (Fin n)) :
      ZMod.stdAddChar (∑ i ∈ s, q (f i) * Multiplicative.toAdd g) =
        ∏ i ∈ s, ZMod.stdAddChar (q (f i) * Multiplicative.toAdd g) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]
  simpa [Function.comp_def] using (hc Finset.univ).symm

omit [NeZero N] in
theorem symmetricCharge_pair (i j : I) :
    symmetricCharge 2 q (TauCeti.Sym.ofFn ![i,j]) = q i+q j := by
  simp [symmetricCharge, TauCeti.Sym.coe_ofFn, List.ofFn_succ]

end
end Math.CyclicWeightCoordinates
