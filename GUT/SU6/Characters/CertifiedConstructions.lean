import GUT.SU6.Representations.FundamentalRepresentation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Constructing torus eigenbasis certificates

This file supplies closure rules for the project-specific
`WeightTheory.TorusEigenbasis` certificate.  The intended finite-dimensional
algebraic representations of `SU(6)` are built from standard blocks by the
usual representation-ring operations; these lemmas let those certificates be
assembled in Lean.
-/

namespace GUT

namespace Flipped
namespace Exp

noncomputable section

theorem evalUnit_add_exp (a b : Exp) (p : AlgebraicTorusPoint) :
    evalUnit (Exp.add a b) p = evalUnit a p * evalUnit b p := by
  cases a with | mk a1 a2 a3 a4 =>
  cases b with | mk b1 b2 b3 b4 =>
  simp [Exp.add, evalUnit, zpow_add, mul_assoc, mul_left_comm]

theorem eval_add_exp (a b : Exp) (p : AlgebraicTorusPoint) :
    eval (Exp.add a b) p = eval a p * eval b p := by
  exact congrArg Units.val (evalUnit_add_exp a b p)

theorem evalUnit_neg_exp (a : Exp) (p : AlgebraicTorusPoint) :
    evalUnit (Exp.neg a) p = (evalUnit a p)⁻¹ := by
  cases a with | mk a1 a2 a3 a4 =>
  simp [Exp.neg, evalUnit, zpow_neg, mul_assoc, mul_comm]

theorem eval_neg_exp (a : Exp) (p : AlgebraicTorusPoint) :
    eval (Exp.neg a) p = (eval a p)⁻¹ := by
  simpa [eval] using congrArg Units.val (evalUnit_neg_exp a p)

theorem eval_ne_zero (a : Exp) (p : AlgebraicTorusPoint) :
    eval a p ≠ 0 :=
  Units.ne_zero (evalUnit a p)

def zeroExp : Exp :=
  { z1 := 0, z2 := 0, z3 := 0, z4 := 0 }

theorem eval_zeroExp (p : AlgebraicTorusPoint) :
    eval zeroExp p = 1 := by
  simp [zeroExp, eval, evalUnit]

@[ext]
theorem ext {a b : Exp}
    (h1 : a.z1 = b.z1) (h2 : a.z2 = b.z2)
    (h3 : a.z3 = b.z3) (h4 : a.z4 = b.z4) : a = b := by
  cases a
  cases b
  simp_all

instance instZero : Zero Exp := ⟨zeroExp⟩
instance instAdd : Add Exp := ⟨Exp.add⟩
instance instNeg : Neg Exp := ⟨Exp.neg⟩
instance instSub : Sub Exp := ⟨fun a b => Exp.add a (Exp.neg b)⟩

instance instAddCommGroup : AddCommGroup Exp where
  zero := zeroExp
  add := Exp.add
  neg := Exp.neg
  sub := fun a b => Exp.add a (Exp.neg b)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    change Exp.add (Exp.add a b) c = Exp.add a (Exp.add b c)
    ext <;> simp [Exp.add, add_assoc]
  zero_add := by
    intro a
    change Exp.add zeroExp a = a
    ext <;> simp [zeroExp, Exp.add]
  add_zero := by
    intro a
    change Exp.add a zeroExp = a
    ext <;> simp [zeroExp, Exp.add]
  neg_add_cancel := by
    intro a
    change Exp.add (Exp.neg a) a = zeroExp
    ext <;> simp [zeroExp, Exp.add, Exp.neg]
  add_comm := by
    intro a b
    change Exp.add a b = Exp.add b a
    ext <;> simp [Exp.add, add_comm]

@[simp]
theorem eval_zero (p : AlgebraicTorusPoint) :
    eval (0 : Exp) p = 1 :=
  eval_zeroExp p

@[simp]
theorem eval_add (a b : Exp) (p : AlgebraicTorusPoint) :
    eval (a + b) p = eval a p * eval b p :=
  eval_add_exp a b p

theorem eval_finset_sum
    {ι : Type*} (s : Finset ι) (w : ι -> Exp)
    (p : AlgebraicTorusPoint) :
    eval (∑ i ∈ s, w i) p =
      ∏ i ∈ s, eval (w i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha, ih]

end

end Exp
end Flipped

namespace CertifiedConstructions

open VirtualRestriction WeightTheory
open scoped TensorProduct BigOperators

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev Actual := VirtualRestriction.ActualSU6Representation

/-- Direct sum/product of two actual finite-dimensional representations. -/
def prodActual (R S : Actual) : Actual where
  V := R.V × S.V
  rho := R.rho.prod S.rho

/-- The one-dimensional trivial actual representation. -/
def trivialActual : Actual where
  V := ℂ
  rho := Representation.trivial ℂ SU6 ℂ

/-- Tensor product of two actual finite-dimensional representations. -/
def tensorActual (R S : Actual) : Actual where
  V := R.V ⊗[ℂ] S.V
  rho := R.rho.tprod S.rho

/-- Exterior powers of an actual finite-dimensional representation. -/
def exteriorActual (R : Actual) (n : ℕ) : Actual where
  V := ⋀[ℂ]^n R.V
  rho :=
    { toFun := fun g => exteriorPower.map n (R.rho g)
      map_one' := by
        rw [R.rho.map_one]
        change exteriorPower.map n (LinearMap.id : R.V →ₗ[ℂ] R.V) = LinearMap.id
        rw [exteriorPower.map_id]
      map_mul' := by
        intro g h
        rw [R.rho.map_mul]
        exact exteriorPower.map_comp (R.rho h) (R.rho g) }

/-- Dual of an actual finite-dimensional representation. -/
def dualActual (R : Actual) : Actual where
  V := Module.Dual ℂ R.V
  rho := R.rho.dual

/-- An invariant subspace, bundled as a mathlib subrepresentation, is an actual representation. -/
def subrepresentationActual (R : Actual) (S : Subrepresentation R.rho) : Actual where
  V := S.toSubmodule
  rho := S.toRepresentation

namespace TorusEigenbasis

/-- The one-dimensional trivial representation is certified with weight zero. -/
def trivial : TorusEigenbasis trivialActual where
  ι := PUnit
  basis := Module.Basis.singleton PUnit ℂ
  weight := fun _ => Flipped.Exp.zeroExp
  action_on_basis := by
    intro t i
    change
      Module.Basis.singleton PUnit ℂ i =
        Flipped.Exp.eval Flipped.Exp.zeroExp t.toAlgebraicTorusPoint •
          Module.Basis.singleton PUnit ℂ i
    rw [Flipped.Exp.eval_zeroExp]
    simp

/-- Transport a torus eigenbasis certificate across an isomorphism of representations. -/
def equiv {R S : Actual}
    (D : TorusEigenbasis R) (e : R.rho.Equiv S.rho) :
    TorusEigenbasis S where
  ι := D.ι
  basis := D.basis.map e.toLinearEquiv
  weight := D.weight
  action_on_basis := by
    intro t i
    have htw :=
      Representation.IntertwiningMap.isIntertwining
        (ρ := R.rho) (σ := S.rho) e.toIntertwiningMap
        t.toDiagonal.toSU6 (D.basis i)
    rw [D.action_on_basis t i] at htw
    simpa [Module.Basis.map_apply] using htw.symm

/--
The subspace spanned by a selected subset of a certified torus eigenbasis.
If it is stable under the full `SU(6)` action, it becomes a certified
subrepresentation below.
-/
def coordinateSubmodule {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) : Submodule ℂ R.V :=
  Submodule.span ℂ (Set.range (fun i : { i // p i } => D.basis i.1))

theorem coordinateSubmodule_eq_span_image {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) :
    coordinateSubmodule D p =
      Submodule.span ℂ (D.basis '' { i | p i }) := by
  unfold coordinateSubmodule
  congr
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem coordinateSubmodule_disjoint {R : Actual}
    (D : TorusEigenbasis R) (p q : D.ι -> Prop)
    (hpq : Disjoint { i | p i } { i | q i }) :
    Disjoint (coordinateSubmodule D p) (coordinateSubmodule D q) := by
  rw [coordinateSubmodule_eq_span_image D p,
    coordinateSubmodule_eq_span_image D q]
  exact D.basis.linearIndependent.disjoint_span_image hpq

theorem coordinateSubmodule_disjoint_compl {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) :
    Disjoint
      (coordinateSubmodule D (fun i => ¬ p i))
      (coordinateSubmodule D p) := by
  apply coordinateSubmodule_disjoint
  exact Set.disjoint_left.mpr (by intro i hni hi; exact hni hi)

def coordinateSubrepresentation {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop)
    (hstable :
      ∀ (g : SU6) ⦃v : R.V⦄,
        v ∈ coordinateSubmodule D p ->
          R.rho g v ∈ coordinateSubmodule D p) :
    Subrepresentation R.rho where
  toSubmodule := coordinateSubmodule D p
  apply_mem_toSubmodule := hstable

def coordinateSubrepresentationActual {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop)
    (hstable :
      ∀ (g : SU6) ⦃v : R.V⦄,
        v ∈ coordinateSubmodule D p ->
          R.rho g v ∈ coordinateSubmodule D p) : Actual :=
  subrepresentationActual R (coordinateSubrepresentation D p hstable)

def coordinateQuotientActual {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop)
    (hstable :
      ∀ (g : SU6) ⦃v : R.V⦄,
        v ∈ coordinateSubmodule D p ->
          R.rho g v ∈ coordinateSubmodule D p) :
    Actual where
  V := R.V ⧸ coordinateSubmodule D p
  rho :=
    R.rho.quotient (coordinateSubmodule D p)
      (by
        intro g v hv
        exact hstable g hv)

def coordinateSubmoduleBasis {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) [DecidablePred p] :
    Module.Basis { i // p i } ℂ (coordinateSubmodule D p) :=
  Module.Basis.span
    (D.basis.linearIndependent.comp
      (fun i : { i // p i } => i.1) Subtype.val_injective)

/--
If a selected subset of a torus eigenbasis spans an `SU(6)`-stable subspace,
the resulting subrepresentation inherits the selected eigenbasis.
-/
def coordinateSubrepresentationEigenbasis {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) [DecidablePred p]
    (hstable :
      ∀ (g : SU6) ⦃v : R.V⦄,
        v ∈ coordinateSubmodule D p ->
          R.rho g v ∈ coordinateSubmodule D p) :
    TorusEigenbasis (coordinateSubrepresentationActual D p hstable) where
  ι := { i // p i }
  basis := coordinateSubmoduleBasis D p
  weight := fun i => D.weight i.1
  action_on_basis := by
    intro t i
    apply Subtype.ext
    change
      R.rho t.toDiagonal.toSU6
          ((coordinateSubmoduleBasis D p i : coordinateSubmodule D p) : R.V) =
        Flipped.Exp.eval (D.weight i.1) t.toAlgebraicTorusPoint •
          ((coordinateSubmoduleBasis D p i : coordinateSubmodule D p) : R.V)
    have hbasis :
        ((coordinateSubmoduleBasis D p i : coordinateSubmodule D p) : R.V) =
          D.basis i.1 := by
      exact Module.Basis.coe_span_apply
        (hli := D.basis.linearIndependent.comp
          (fun i : { i // p i } => i.1) Subtype.val_injective) i
    rw [hbasis]
    exact D.action_on_basis t i.1

def coordinateQuotientBasis {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) [DecidablePred p] :
    Module.Basis { i // ¬ p i } ℂ (R.V ⧸ coordinateSubmodule D p) :=
  Module.Basis.mk
    (v := fun i : { i // ¬ p i } =>
      (coordinateSubmodule D p).mkQ (D.basis i.1))
    (by
      have hliComp :
          LinearIndependent ℂ
            (fun i : { i // ¬ p i } => D.basis i.1) :=
        D.basis.linearIndependent.comp
          (fun i : { i // ¬ p i } => i.1) Subtype.val_injective
      have hdis :
          Disjoint
            (Submodule.span ℂ
              (Set.range (fun i : { i // ¬ p i } => D.basis i.1)))
            (LinearMap.ker (coordinateSubmodule D p).mkQ) := by
        rw [Submodule.ker_mkQ]
        exact coordinateSubmodule_disjoint_compl D p
      simpa [Function.comp_def] using
        hliComp.map (f := (coordinateSubmodule D p).mkQ) hdis)
    (by
      intro x _hx
      rcases (Submodule.mkQ_surjective (coordinateSubmodule D p)) x with ⟨v, rfl⟩
      rw [← D.basis.sum_repr v]
      rw [map_sum]
      apply Submodule.sum_mem
      intro i _hi
      rw [map_smul]
      by_cases hp : p i
      · have hzero : (coordinateSubmodule D p).mkQ (D.basis i) = 0 := by
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact Submodule.subset_span ⟨⟨i, hp⟩, rfl⟩
        simp [hzero]
      · apply Submodule.smul_mem
        exact Submodule.subset_span
          (show
            (coordinateSubmodule D p).mkQ (D.basis i) ∈
              Set.range (fun j : { j // ¬ p j } =>
                (coordinateSubmodule D p).mkQ (D.basis j.1)) from
            ⟨⟨i, hp⟩, rfl⟩))

/--
If a selected subset of a torus eigenbasis spans an `SU(6)`-stable subspace,
the coordinate quotient by that subspace inherits the complementary eigenbasis.
-/
def coordinateQuotientEigenbasis {R : Actual}
    (D : TorusEigenbasis R) (p : D.ι -> Prop) [DecidablePred p]
    (hstable :
      ∀ (g : SU6) ⦃v : R.V⦄,
        v ∈ coordinateSubmodule D p ->
          R.rho g v ∈ coordinateSubmodule D p) :
    TorusEigenbasis (coordinateQuotientActual D p hstable) where
  ι := { i // ¬ p i }
  basis := coordinateQuotientBasis D p
  weight := fun i => D.weight i.1
  action_on_basis := by
    intro t i
    let W := coordinateSubmodule D p
    change
      (R.rho.quotient W
          (by
            intro g v hv
            exact hstable g hv)) t.toDiagonal.toSU6
          (coordinateQuotientBasis D p i) =
        Flipped.Exp.eval (D.weight i.1) t.toAlgebraicTorusPoint •
          coordinateQuotientBasis D p i
    rw [coordinateQuotientBasis, Module.Basis.mk_apply]
    change
      W.mkQ (R.rho t.toDiagonal.toSU6 (D.basis i.1)) =
        Flipped.Exp.eval (D.weight i.1) t.toAlgebraicTorusPoint •
          W.mkQ (D.basis i.1)
    rw [D.action_on_basis t i.1]
    rw [map_smul]

/-- A product/direct-sum of certified representations is certified. -/
def prod {R S : Actual}
    (DR : TorusEigenbasis R) (DS : TorusEigenbasis S) :
    TorusEigenbasis (prodActual R S) where
  ι := DR.ι ⊕ DS.ι
  basis := DR.basis.prod DS.basis
  weight := Sum.elim DR.weight DS.weight
  action_on_basis := by
    intro t i
    cases i with
    | inl i =>
        change
          (R.rho.prod S.rho) t.toDiagonal.toSU6
              (DR.basis.prod DS.basis (Sum.inl i)) =
            Flipped.Exp.eval (DR.weight i) t.toAlgebraicTorusPoint •
              DR.basis.prod DS.basis (Sum.inl i)
        ext <;> simp [Module.Basis.prod_apply, DR.action_on_basis t i]
    | inr j =>
        change
          (R.rho.prod S.rho) t.toDiagonal.toSU6
              (DR.basis.prod DS.basis (Sum.inr j)) =
            Flipped.Exp.eval (DS.weight j) t.toAlgebraicTorusPoint •
              DR.basis.prod DS.basis (Sum.inr j)
        ext <;> simp [Module.Basis.prod_apply, DS.action_on_basis t j]

/-- A tensor product of certified representations is certified. -/
def tensor {R S : Actual}
    (DR : TorusEigenbasis R) (DS : TorusEigenbasis S) :
    TorusEigenbasis (tensorActual R S) where
  ι := DR.ι × DS.ι
  basis := DR.basis.tensorProduct DS.basis
  weight := fun ij => Flipped.Exp.add (DR.weight ij.1) (DS.weight ij.2)
  action_on_basis := by
    intro t ij
    rcases ij with ⟨i, j⟩
    have h :
        TensorProduct.map (R.rho t.toDiagonal.toSU6) (S.rho t.toDiagonal.toSU6)
            (DR.basis i ⊗ₜ[ℂ] DS.basis j) =
          Flipped.Exp.eval (Flipped.Exp.add (DR.weight i) (DS.weight j))
              t.toAlgebraicTorusPoint •
            (DR.basis i ⊗ₜ[ℂ] DS.basis j) := by
      rw [TensorProduct.map_tmul, DR.action_on_basis t i, DS.action_on_basis t j,
        Flipped.Exp.eval_add_exp]
      exact TensorProduct.smul_tmul_smul
        (Flipped.Exp.eval (DR.weight i) t.toAlgebraicTorusPoint)
        (Flipped.Exp.eval (DS.weight j) t.toAlgebraicTorusPoint)
        (DR.basis i) (DS.basis j)
    change
      (R.rho.tprod S.rho) t.toDiagonal.toSU6
          (DR.basis.tensorProduct DS.basis (i, j)) =
        Flipped.Exp.eval (Flipped.Exp.add (DR.weight i) (DS.weight j))
            t.toAlgebraicTorusPoint •
          DR.basis.tensorProduct DS.basis (i, j)
    simpa [Module.Basis.tensorProduct_apply, Representation.tprod_apply] using h

theorem prod_ofFinEmbEquiv_symm_eq
    {I M : Type*} [LinearOrder I] [CommMonoid M]
    {n : ℕ} (s : Set.powersetCard I n) (f : I -> M) :
    (∏ k : Fin n, f (Set.powersetCard.ofFinEmbEquiv.symm s k)) =
      ∏ i ∈ (s : Finset I), f i := by
  change
    (∏ k : Fin n,
        f (((s : Finset I).orderEmbOfFin (Set.powersetCard.card_eq s)) k)) =
      ∏ i ∈ (s : Finset I), f i
  let e := ((s : Finset I).orderEmbOfFin
    (Set.powersetCard.card_eq s)).toEmbedding
  calc
    (∏ k : Fin n,
        f (((s : Finset I).orderEmbOfFin (Set.powersetCard.card_eq s)) k)) =
        ∏ k ∈ (Finset.univ : Finset (Fin n)), f (e k) := by
          simp [e]
    _ = ∏ i ∈ Finset.map e (Finset.univ : Finset (Fin n)), f i := by
          exact (Finset.prod_map (Finset.univ : Finset (Fin n)) e f).symm
    _ = ∏ i ∈ (s : Finset I), f i := by
          rw [Finset.map_orderEmbOfFin_univ]

def exteriorWeight {R : Actual}
    (D : TorusEigenbasis R) [LinearOrder D.ι]
    (n : ℕ) (s : Set.powersetCard D.ι n) : Flipped.Exp :=
  ∑ i ∈ (s : Finset D.ι), D.weight i

/--
Exterior powers of certified representations are certified: the wedge basis is
an eigenbasis and the wedge weight is the sum of the selected weights.
-/
def exterior {R : Actual}
    (D : TorusEigenbasis R) [LinearOrder D.ι]
    (n : ℕ) :
    TorusEigenbasis (exteriorActual R n) where
  ι := Set.powersetCard D.ι n
  basis := D.basis.exteriorPower n
  weight := exteriorWeight D n
  action_on_basis := by
    intro t s
    let g : SU6 := t.toDiagonal.toSU6
    let lam : D.ι -> ℂ :=
      fun i => Flipped.Exp.eval (D.weight i) t.toAlgebraicTorusPoint
    let emb := Set.powersetCard.ofFinEmbEquiv.symm s
    have hmap :
        (exteriorPower.map n (R.rho g))
            (exteriorPower.ιMulti_family ℂ n D.basis s) =
          exteriorPower.ιMulti ℂ n
            (fun k : Fin n => (lam (emb k)) • D.basis (emb k)) := by
      rw [exteriorPower.map_apply_ιMulti_family]
      change
        exteriorPower.ιMulti ℂ n
            (fun k : Fin n => R.rho g (D.basis (emb k))) =
          exteriorPower.ιMulti ℂ n
            (fun k : Fin n => (lam (emb k)) • D.basis (emb k))
      apply congrArg (exteriorPower.ιMulti ℂ n (M := R.V))
      funext k
      exact D.action_on_basis t (emb k)
    have hsmul :
        exteriorPower.ιMulti ℂ n
            (fun k : Fin n => (lam (emb k)) • D.basis (emb k)) =
          (∏ k : Fin n, lam (emb k)) •
            exteriorPower.ιMulti ℂ n (fun k : Fin n => D.basis (emb k)) := by
      exact AlternatingMap.map_smul_univ
        (exteriorPower.ιMulti ℂ n (M := R.V))
        (fun k : Fin n => lam (emb k))
        (fun k : Fin n => D.basis (emb k))
    have hprod :
        (∏ k : Fin n, lam (emb k)) =
          ∏ i ∈ (s : Finset D.ι), lam i := by
      simpa [emb] using prod_ofFinEmbEquiv_symm_eq s lam
    have hweight :
        Flipped.Exp.eval (exteriorWeight D n s) t.toAlgebraicTorusPoint =
          ∏ i ∈ (s : Finset D.ι), lam i := by
      simpa [exteriorWeight, lam] using
        Flipped.Exp.eval_finset_sum
          (s : Finset D.ι) D.weight t.toAlgebraicTorusPoint
    change
      exteriorPower.map n (R.rho g) (D.basis.exteriorPower n s) =
        Flipped.Exp.eval (exteriorWeight D n s) t.toAlgebraicTorusPoint •
          D.basis.exteriorPower n s
    rw [exteriorPower.basis_apply, hmap, hsmul, hprod, hweight]
    rfl

theorem action_inv_on_basis {R : Actual}
    (D : TorusEigenbasis R)
    (t : FlippedTorus.FlippedDiagonalSU6Point) (i : D.ι) :
    R.rho (t.toDiagonal.toSU6⁻¹) (D.basis i) =
      (Flipped.Exp.eval (D.weight i) t.toAlgebraicTorusPoint)⁻¹ •
        D.basis i := by
  let g : SU6 := t.toDiagonal.toSU6
  let lam : ℂ := Flipped.Exp.eval (D.weight i) t.toAlgebraicTorusPoint
  have hlam : lam ≠ 0 := by
    simpa [lam] using Flipped.Exp.eval_ne_zero (D.weight i) t.toAlgebraicTorusPoint
  have hact : R.rho g (D.basis i) = lam • D.basis i := by
    simpa [g, lam] using D.action_on_basis t i
  apply (R.rho.apply_bijective g).injective
  have hright : R.rho g (lam⁻¹ • D.basis i) = D.basis i := by
    rw [map_smul, hact, smul_smul]
    simp [hlam]
  calc
    R.rho g (R.rho g⁻¹ (D.basis i)) = D.basis i := by
      simp [g]
    _ = R.rho g (lam⁻¹ • D.basis i) := hright.symm

/-- The dual of a certified representation is certified, with negated weights. -/
def dual {R : Actual}
    (D : TorusEigenbasis R) :
    TorusEigenbasis (dualActual R) where
  ι := D.ι
  basis := D.basis.dualBasis
  weight := fun i => Flipped.Exp.neg (D.weight i)
  action_on_basis := by
    intro t i
    apply D.basis.ext
    intro j
    have hinv := action_inv_on_basis D t j
    by_cases hji : j = i
    · subst j
      change
        D.basis.dualBasis i (R.rho (t.toDiagonal.toSU6⁻¹) (D.basis i)) =
          (Flipped.Exp.eval (Flipped.Exp.neg (D.weight i))
              t.toAlgebraicTorusPoint • D.basis.dualBasis i) (D.basis i)
      rw [hinv]
      simp [Flipped.Exp.eval_neg_exp]
    · have hij : i ≠ j := fun hij => hji hij.symm
      change
        D.basis.dualBasis i (R.rho (t.toDiagonal.toSU6⁻¹) (D.basis j)) =
          (Flipped.Exp.eval (Flipped.Exp.neg (D.weight i))
              t.toAlgebraicTorusPoint • D.basis.dualBasis i) (D.basis j)
      rw [hinv]
      simp [hij]

end TorusEigenbasis

/-- A certified actual representation, packaged as the physical cut used downstream. -/
def physicallyAdmissibleOfEigenbasis
    {R : Actual} (D : TorusEigenbasis R) :
    PhysicallyAdmissibleSU6Representation where
  toActual := R
  eigenbasis := D

/-- Direct sums/products preserve the physical admissibility cut. -/
def PhysicallyAdmissibleSU6Representation.prod
    (R S : PhysicallyAdmissibleSU6Representation) :
    PhysicallyAdmissibleSU6Representation where
  toActual := prodActual R.toActual S.toActual
  eigenbasis := TorusEigenbasis.prod R.eigenbasis S.eigenbasis

/-- Tensor products preserve the physical admissibility cut. -/
def PhysicallyAdmissibleSU6Representation.tensor
    (R S : PhysicallyAdmissibleSU6Representation) :
    PhysicallyAdmissibleSU6Representation where
  toActual := tensorActual R.toActual S.toActual
  eigenbasis := TorusEigenbasis.tensor R.eigenbasis S.eigenbasis

/-- Exterior powers preserve the physical admissibility cut. -/
def PhysicallyAdmissibleSU6Representation.exterior
    (R : PhysicallyAdmissibleSU6Representation) (n : ℕ) :
    PhysicallyAdmissibleSU6Representation where
  toActual := exteriorActual R.toActual n
  eigenbasis := by
    letI : LinearOrder R.eigenbasis.ι := WellOrderingRel.isWellOrder.linearOrder
    exact TorusEigenbasis.exterior R.eigenbasis n

/-- Duals preserve the physical admissibility cut. -/
def PhysicallyAdmissibleSU6Representation.dual
    (R : PhysicallyAdmissibleSU6Representation) :
    PhysicallyAdmissibleSU6Representation where
  toActual := dualActual R.toActual
  eigenbasis := TorusEigenbasis.dual R.eigenbasis

/-- Representation isomorphisms preserve the physical admissibility cut. -/
def PhysicallyAdmissibleSU6Representation.equiv
    (R : PhysicallyAdmissibleSU6Representation) {S : Actual}
    (e : R.toActual.rho.Equiv S.rho) :
    PhysicallyAdmissibleSU6Representation where
  toActual := S
  eigenbasis := TorusEigenbasis.equiv R.eigenbasis e

/--
An `SU(6)`-stable coordinate subspace spanned by selected eigenbasis vectors
inherits physical admissibility.
-/
def PhysicallyAdmissibleSU6Representation.coordinateSubrepresentation
    (R : PhysicallyAdmissibleSU6Representation)
    (p : R.eigenbasis.ι -> Prop) [DecidablePred p]
    (hstable :
      ∀ (g : SU6) ⦃v : R.toActual.V⦄,
        v ∈ TorusEigenbasis.coordinateSubmodule R.eigenbasis p ->
          R.toActual.rho g v ∈
            TorusEigenbasis.coordinateSubmodule R.eigenbasis p) :
    PhysicallyAdmissibleSU6Representation where
  toActual :=
    TorusEigenbasis.coordinateSubrepresentationActual R.eigenbasis p hstable
  eigenbasis :=
    TorusEigenbasis.coordinateSubrepresentationEigenbasis R.eigenbasis p hstable

/--
An `SU(6)`-stable coordinate subspace can also be quotiented out; the quotient
inherits the complementary torus eigenbasis.
-/
def PhysicallyAdmissibleSU6Representation.coordinateQuotient
    (R : PhysicallyAdmissibleSU6Representation)
    (p : R.eigenbasis.ι -> Prop) [DecidablePred p]
    (hstable :
      ∀ (g : SU6) ⦃v : R.toActual.V⦄,
        v ∈ TorusEigenbasis.coordinateSubmodule R.eigenbasis p ->
          R.toActual.rho g v ∈
            TorusEigenbasis.coordinateSubmodule R.eigenbasis p) :
    PhysicallyAdmissibleSU6Representation where
  toActual :=
    TorusEigenbasis.coordinateQuotientActual R.eigenbasis p hstable
  eigenbasis :=
    TorusEigenbasis.coordinateQuotientEigenbasis R.eigenbasis p hstable

/--
Finite virtual combinations whose summands each carry an explicit torus
eigenbasis certificate.  This is the strongest currently kernel-checked
replacement for a global `SU6TorusEigenbasisTheory`.
-/
structure PhysicallyAdmissibleVirtualSummand where
  coeff : Int
  rep : PhysicallyAdmissibleSU6Representation

namespace PhysicallyAdmissibleVirtualSummand

def toVirtualSummand
    (s : PhysicallyAdmissibleVirtualSummand) :
    VirtualRestriction.VirtualSummand where
  coeff := s.coeff
  rep := s.rep.toActual

def normalizedPoly (s : PhysicallyAdmissibleVirtualSummand) :
    Flipped.Normalized.Poly :=
  Flipped.Normalized.zscale s.coeff (s.rep.normalizedCharacter).poly

theorem normalizedPoly_evaluates
    (s : PhysicallyAdmissibleVirtualSummand)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        s.normalizedPoly t =
      s.toVirtualSummand.restrictedCharacter t := by
  rw [normalizedPoly, NormalizedVirtualRestriction.commonLaurentEvaluator.eval_zscale,
    NormalizedVirtualRestriction.commonLaurentEvaluator]
  change
    (s.coeff : ℂ) *
        NormalizedVirtualRestriction.diagonalLaurentEval
          (s.rep.normalizedCharacter).poly t =
      s.toVirtualSummand.restrictedCharacter t
  rw [(s.rep.normalizedCharacter).evaluates_restrictedCharacter]
  rfl

end PhysicallyAdmissibleVirtualSummand

abbrev FinitePhysicallyAdmissibleVirtualSU6Representation :=
  List PhysicallyAdmissibleVirtualSummand

namespace FinitePhysicallyAdmissibleVirtualSU6Representation

def toFiniteVirtual :
    FinitePhysicallyAdmissibleVirtualSU6Representation ->
      VirtualRestriction.FiniteVirtualSU6Representation
  | [] => []
  | s :: ss => s.toVirtualSummand :: toFiniteVirtual ss

def normalizedPoly :
    FinitePhysicallyAdmissibleVirtualSU6Representation ->
      Flipped.Normalized.Poly
  | [] => 0
  | s :: ss => s.normalizedPoly + normalizedPoly ss

theorem normalizedPoly_evaluates
    (χ : FinitePhysicallyAdmissibleVirtualSU6Representation)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        (normalizedPoly χ) t =
      VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
        (toFiniteVirtual χ) t := by
  induction χ with
  | nil =>
      rw [normalizedPoly, toFiniteVirtual,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        NormalizedVirtualRestriction.commonLaurentEvaluator.eval_zero]
  | cons s ss ih =>
      rw [normalizedPoly, toFiniteVirtual,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        NormalizedVirtualRestriction.commonLaurentEvaluator.eval_add,
        s.normalizedPoly_evaluates, ih]

theorem normalizedPoly_swap36_fixed
    (χ : FinitePhysicallyAdmissibleVirtualSU6Representation) :
    Flipped.Normalized.swap36 (normalizedPoly χ) = normalizedPoly χ := by
  apply NormalizedVirtualRestriction.commonLaurentEvaluator.faithful
  intro t
  rw [NormalizedVirtualRestriction.commonLaurentEvaluator.eval_swap36,
    normalizedPoly_evaluates, normalizedPoly_evaluates,
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed]

theorem normalizedPoly_ne_flippedSMCharacter
    (χ : FinitePhysicallyAdmissibleVirtualSU6Representation) :
    normalizedPoly χ ≠ Flipped.Normalized.flippedSMCharacter := by
  intro h
  have hfixed := normalizedPoly_swap36_fixed χ
  rw [h] at hfixed
  exact Flipped.Normalized.swap36_flippedSMCharacter_ne hfixed

theorem no_flippedSM_uplift :
    ¬ ∃ χ : FinitePhysicallyAdmissibleVirtualSU6Representation,
      normalizedPoly χ = Flipped.Normalized.flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact normalizedPoly_ne_flippedSMCharacter χ hχ

end FinitePhysicallyAdmissibleVirtualSU6Representation

/--
The constructive class currently Lean-certified in this project: start from the
defining `SU(6)` representation and close under direct sum/product, tensor
product, exterior powers, and dual.

This is a deliberately narrower formal cut than "all abstract finite-dimensional
group representations"; it matches the algebraic/tensor-generated
representations used in the representation ring.
-/
inductive TensorGeneratedSU6Representation where
  | trivial : TensorGeneratedSU6Representation
  | fundamental : TensorGeneratedSU6Representation
  | prod :
      TensorGeneratedSU6Representation ->
      TensorGeneratedSU6Representation ->
      TensorGeneratedSU6Representation
  | tensor :
      TensorGeneratedSU6Representation ->
      TensorGeneratedSU6Representation ->
      TensorGeneratedSU6Representation
  | exterior :
      TensorGeneratedSU6Representation ->
      ℕ ->
      TensorGeneratedSU6Representation
  | dual :
      TensorGeneratedSU6Representation ->
      TensorGeneratedSU6Representation

namespace TensorGeneratedSU6Representation

def toPhysicallyAdmissible :
    TensorGeneratedSU6Representation -> PhysicallyAdmissibleSU6Representation
  | trivial => physicallyAdmissibleOfEigenbasis TorusEigenbasis.trivial
  | fundamental => FundamentalRepresentation.physicallyAdmissible
  | prod R S =>
      PhysicallyAdmissibleSU6Representation.prod
        (toPhysicallyAdmissible R) (toPhysicallyAdmissible S)
  | tensor R S =>
      PhysicallyAdmissibleSU6Representation.tensor
        (toPhysicallyAdmissible R) (toPhysicallyAdmissible S)
  | exterior R n =>
      PhysicallyAdmissibleSU6Representation.exterior
        (toPhysicallyAdmissible R) n
  | dual R =>
      PhysicallyAdmissibleSU6Representation.dual (toPhysicallyAdmissible R)

def toActual (R : TensorGeneratedSU6Representation) : Actual :=
  R.toPhysicallyAdmissible.toActual

def eigenbasis (R : TensorGeneratedSU6Representation) :
    TorusEigenbasis R.toActual :=
  R.toPhysicallyAdmissible.eigenbasis

theorem normalizedCharacter_evaluates
    (R : TensorGeneratedSU6Representation)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.diagonalLaurentEval
        (R.toPhysicallyAdmissible.normalizedCharacter).poly t =
      R.toActual.restrictedCharacter t := by
  exact
    (R.toPhysicallyAdmissible.normalizedCharacter).evaluates_restrictedCharacter t

end TensorGeneratedSU6Representation

/--
Certificate that an actual representation is isomorphic to an `SU(6)`-stable
coordinate subrepresentation of a tensor/exterior-generated ambient
representation.
-/
structure TensorGeneratedCoordinateSubrepresentationCertificate
    (S : Actual) where
  ambient : TensorGeneratedSU6Representation
  p : ambient.eigenbasis.ι -> Prop
  [decidablePred : DecidablePred p]
  hstable :
    ∀ (g : SU6) ⦃v : ambient.toActual.V⦄,
      v ∈ TorusEigenbasis.coordinateSubmodule ambient.eigenbasis p ->
        ambient.toActual.rho g v ∈
          TorusEigenbasis.coordinateSubmodule ambient.eigenbasis p
  equivTo :
    (TorusEigenbasis.coordinateSubrepresentationActual
      ambient.eigenbasis p hstable).rho.Equiv S.rho

attribute [instance]
  TensorGeneratedCoordinateSubrepresentationCertificate.decidablePred

namespace TensorGeneratedCoordinateSubrepresentationCertificate

def eigenbasis {S : Actual}
    (c : TensorGeneratedCoordinateSubrepresentationCertificate S) :
    TorusEigenbasis S := by
  haveI : DecidablePred c.p := c.decidablePred
  exact
    TorusEigenbasis.equiv
      (TorusEigenbasis.coordinateSubrepresentationEigenbasis
        c.ambient.eigenbasis c.p c.hstable)
      c.equivTo

def toPhysicallyAdmissible {S : Actual}
    (c : TensorGeneratedCoordinateSubrepresentationCertificate S) :
    PhysicallyAdmissibleSU6Representation where
  toActual := S
  eigenbasis := c.eigenbasis

end TensorGeneratedCoordinateSubrepresentationCertificate

/--
Certificate that an actual representation is isomorphic to a coordinate
quotient of a tensor/exterior-generated ambient representation by an
`SU(6)`-stable coordinate subspace.
-/
structure TensorGeneratedCoordinateQuotientCertificate
    (S : Actual) where
  ambient : TensorGeneratedSU6Representation
  p : ambient.eigenbasis.ι -> Prop
  [decidablePred : DecidablePred p]
  hstable :
    ∀ (g : SU6) ⦃v : ambient.toActual.V⦄,
      v ∈ TorusEigenbasis.coordinateSubmodule ambient.eigenbasis p ->
        ambient.toActual.rho g v ∈
          TorusEigenbasis.coordinateSubmodule ambient.eigenbasis p
  equivTo :
    (TorusEigenbasis.coordinateQuotientActual
      ambient.eigenbasis p hstable).rho.Equiv S.rho

attribute [instance]
  TensorGeneratedCoordinateQuotientCertificate.decidablePred

namespace TensorGeneratedCoordinateQuotientCertificate

def eigenbasis {S : Actual}
    (c : TensorGeneratedCoordinateQuotientCertificate S) :
    TorusEigenbasis S := by
  haveI : DecidablePred c.p := c.decidablePred
  exact
    TorusEigenbasis.equiv
      (TorusEigenbasis.coordinateQuotientEigenbasis
        c.ambient.eigenbasis c.p c.hstable)
      c.equivTo

def toPhysicallyAdmissible {S : Actual}
    (c : TensorGeneratedCoordinateQuotientCertificate S) :
    PhysicallyAdmissibleSU6Representation where
  toActual := S
  eigenbasis := c.eigenbasis

end TensorGeneratedCoordinateQuotientCertificate

/--
The next formal cut toward highest-weight representation theory: a
representation is accepted if it is tensor/exterior-generated itself, or if it
is a stable coordinate subrepresentation/quotient of one, up to representation
isomorphism.
-/
inductive TensorGeneratedSubquotientCertificate (S : Actual) where
  | ofTensorGenerated
      (R : TensorGeneratedSU6Representation)
      (e : R.toActual.rho.Equiv S.rho) :
      TensorGeneratedSubquotientCertificate S
  | ofCoordinateSubrepresentation
      (c : TensorGeneratedCoordinateSubrepresentationCertificate S) :
      TensorGeneratedSubquotientCertificate S
  | ofCoordinateQuotient
      (c : TensorGeneratedCoordinateQuotientCertificate S) :
      TensorGeneratedSubquotientCertificate S

namespace TensorGeneratedSubquotientCertificate

def eigenbasis {S : Actual}
    (c : TensorGeneratedSubquotientCertificate S) :
    TorusEigenbasis S :=
  match c with
  | .ofTensorGenerated R e =>
      TorusEigenbasis.equiv R.eigenbasis e
  | .ofCoordinateSubrepresentation c =>
      c.eigenbasis
  | .ofCoordinateQuotient c =>
      c.eigenbasis

def toPhysicallyAdmissible {S : Actual}
    (c : TensorGeneratedSubquotientCertificate S) :
    PhysicallyAdmissibleSU6Representation where
  toActual := S
  eigenbasis := c.eigenbasis

end TensorGeneratedSubquotientCertificate

/--
A bundled actual representation equipped with a tensor/exterior-generated
subquotient certificate.  This is the Lean-ready proxy for the standard
highest-weight realization of algebraic `SU(6)` representations as subquotients
of tensor constructions.
-/
structure TensorGeneratedSubquotientSU6Representation where
  toActual : Actual
  certificate : TensorGeneratedSubquotientCertificate toActual

namespace TensorGeneratedSubquotientSU6Representation

def toPhysicallyAdmissible
    (R : TensorGeneratedSubquotientSU6Representation) :
    PhysicallyAdmissibleSU6Representation where
  toActual := R.toActual
  eigenbasis := R.certificate.eigenbasis

def normalizedCharacter
    (R : TensorGeneratedSubquotientSU6Representation) :
    NormalizedVirtualRestriction.ActualTorusWeightCharacter R.toActual :=
  R.toPhysicallyAdmissible.normalizedCharacter

theorem normalizedCharacter_evaluates
    (R : TensorGeneratedSubquotientSU6Representation)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.diagonalLaurentEval
        (R.normalizedCharacter).poly t =
      R.toActual.restrictedCharacter t := by
  exact (R.normalizedCharacter).evaluates_restrictedCharacter t

end TensorGeneratedSubquotientSU6Representation

structure TensorGeneratedVirtualSummand where
  coeff : Int
  rep : TensorGeneratedSU6Representation

namespace TensorGeneratedVirtualSummand

def toVirtualSummand
    (s : TensorGeneratedVirtualSummand) : VirtualRestriction.VirtualSummand where
  coeff := s.coeff
  rep := s.rep.toActual

def normalizedPoly (s : TensorGeneratedVirtualSummand) :
    Flipped.Normalized.Poly :=
  Flipped.Normalized.zscale s.coeff
    (s.rep.toPhysicallyAdmissible.normalizedCharacter).poly

theorem normalizedPoly_evaluates
    (s : TensorGeneratedVirtualSummand)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        s.normalizedPoly t =
      s.toVirtualSummand.restrictedCharacter t := by
  rw [normalizedPoly, NormalizedVirtualRestriction.commonLaurentEvaluator.eval_zscale,
    NormalizedVirtualRestriction.commonLaurentEvaluator]
  change
    (s.coeff : ℂ) *
        NormalizedVirtualRestriction.diagonalLaurentEval
          (s.rep.toPhysicallyAdmissible.normalizedCharacter).poly t =
      s.toVirtualSummand.restrictedCharacter t
  rw [TensorGeneratedSU6Representation.normalizedCharacter_evaluates]
  rfl

end TensorGeneratedVirtualSummand

abbrev FiniteTensorGeneratedVirtualSU6Representation :=
  List TensorGeneratedVirtualSummand

namespace FiniteTensorGeneratedVirtualSU6Representation

def toFiniteVirtual :
    FiniteTensorGeneratedVirtualSU6Representation ->
      VirtualRestriction.FiniteVirtualSU6Representation
  | [] => []
  | s :: ss => s.toVirtualSummand :: toFiniteVirtual ss

def normalizedPoly :
    FiniteTensorGeneratedVirtualSU6Representation ->
      Flipped.Normalized.Poly
  | [] => 0
  | s :: ss => s.normalizedPoly + normalizedPoly ss

theorem normalizedPoly_evaluates
    (χ : FiniteTensorGeneratedVirtualSU6Representation)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        (normalizedPoly χ) t =
      VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
        (toFiniteVirtual χ) t := by
  induction χ with
  | nil =>
      rw [normalizedPoly, toFiniteVirtual,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        NormalizedVirtualRestriction.commonLaurentEvaluator.eval_zero]
  | cons s ss ih =>
      rw [normalizedPoly, toFiniteVirtual,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        NormalizedVirtualRestriction.commonLaurentEvaluator.eval_add,
        s.normalizedPoly_evaluates, ih]

theorem normalizedPoly_swap36_fixed
    (χ : FiniteTensorGeneratedVirtualSU6Representation) :
    Flipped.Normalized.swap36 (normalizedPoly χ) = normalizedPoly χ := by
  apply NormalizedVirtualRestriction.commonLaurentEvaluator.faithful
  intro t
  rw [NormalizedVirtualRestriction.commonLaurentEvaluator.eval_swap36,
    normalizedPoly_evaluates, normalizedPoly_evaluates,
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed]

theorem normalizedPoly_ne_flippedSMCharacter
    (χ : FiniteTensorGeneratedVirtualSU6Representation) :
    normalizedPoly χ ≠ Flipped.Normalized.flippedSMCharacter := by
  intro h
  have hfixed := normalizedPoly_swap36_fixed χ
  rw [h] at hfixed
  exact Flipped.Normalized.swap36_flippedSMCharacter_ne hfixed

theorem no_flippedSM_uplift :
    ¬ ∃ χ : FiniteTensorGeneratedVirtualSU6Representation,
      normalizedPoly χ = Flipped.Normalized.flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact normalizedPoly_ne_flippedSMCharacter χ hχ

end FiniteTensorGeneratedVirtualSU6Representation

/--
A finite virtual summand whose actual representation is supplied by a
tensor/exterior-generated subquotient certificate.
-/
structure TensorGeneratedSubquotientVirtualSummand where
  coeff : Int
  rep : TensorGeneratedSubquotientSU6Representation

namespace TensorGeneratedSubquotientVirtualSummand

def toPhysicallyAdmissibleSummand
    (s : TensorGeneratedSubquotientVirtualSummand) :
    PhysicallyAdmissibleVirtualSummand where
  coeff := s.coeff
  rep := s.rep.toPhysicallyAdmissible

def toVirtualSummand
    (s : TensorGeneratedSubquotientVirtualSummand) :
    VirtualRestriction.VirtualSummand :=
  s.toPhysicallyAdmissibleSummand.toVirtualSummand

def normalizedPoly (s : TensorGeneratedSubquotientVirtualSummand) :
    Flipped.Normalized.Poly :=
  s.toPhysicallyAdmissibleSummand.normalizedPoly

theorem normalizedPoly_evaluates
    (s : TensorGeneratedSubquotientVirtualSummand)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        s.normalizedPoly t =
      s.toVirtualSummand.restrictedCharacter t := by
  exact s.toPhysicallyAdmissibleSummand.normalizedPoly_evaluates t

end TensorGeneratedSubquotientVirtualSummand

abbrev FiniteTensorGeneratedSubquotientVirtualSU6Representation :=
  List TensorGeneratedSubquotientVirtualSummand

namespace FiniteTensorGeneratedSubquotientVirtualSU6Representation

def toFinitePhysicallyAdmissible :
    FiniteTensorGeneratedSubquotientVirtualSU6Representation ->
      FinitePhysicallyAdmissibleVirtualSU6Representation
  | [] => []
  | s :: ss =>
      s.toPhysicallyAdmissibleSummand :: toFinitePhysicallyAdmissible ss

def toFiniteVirtual
    (χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation) :
    VirtualRestriction.FiniteVirtualSU6Representation :=
  FinitePhysicallyAdmissibleVirtualSU6Representation.toFiniteVirtual
    (toFinitePhysicallyAdmissible χ)

def normalizedPoly
    (χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation) :
    Flipped.Normalized.Poly :=
  FinitePhysicallyAdmissibleVirtualSU6Representation.normalizedPoly
    (toFinitePhysicallyAdmissible χ)

theorem normalizedPoly_evaluates
    (χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation)
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.commonLaurentEvaluator.eval
        (normalizedPoly χ) t =
      VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
        (toFiniteVirtual χ) t := by
  exact
    FinitePhysicallyAdmissibleVirtualSU6Representation.normalizedPoly_evaluates
      (toFinitePhysicallyAdmissible χ) t

theorem normalizedPoly_swap36_fixed
    (χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation) :
    Flipped.Normalized.swap36 (normalizedPoly χ) = normalizedPoly χ := by
  exact
    FinitePhysicallyAdmissibleVirtualSU6Representation.normalizedPoly_swap36_fixed
      (toFinitePhysicallyAdmissible χ)

theorem normalizedPoly_ne_flippedSMCharacter
    (χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation) :
    normalizedPoly χ ≠ Flipped.Normalized.flippedSMCharacter := by
  exact
    FinitePhysicallyAdmissibleVirtualSU6Representation.normalizedPoly_ne_flippedSMCharacter
      (toFinitePhysicallyAdmissible χ)

theorem no_flippedSM_uplift :
    ¬ ∃ χ : FiniteTensorGeneratedSubquotientVirtualSU6Representation,
      normalizedPoly χ = Flipped.Normalized.flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact normalizedPoly_ne_flippedSMCharacter χ hχ

end FiniteTensorGeneratedSubquotientVirtualSU6Representation

end

end CertifiedConstructions
end GUT
