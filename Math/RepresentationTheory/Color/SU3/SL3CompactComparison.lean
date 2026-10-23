import Math.LieGroups.SpecialLinear.ColorPlanes
import Math.RepresentationTheory.SU2.SL2SpannedProducts
import Math.RepresentationTheory.Color.SU3.SU3TensorPositive

/-! Algebraic compact-to-complex comparison for the actual mixed color tensor
spaces. All three plane-spanning hypotheses are constructed, not supplied. -/
namespace Math.SL3CompactComparison
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL2SymmetricSpan
open scoped TensorProduct

abbrev Vector := Fin 3 → ℂ

def standard : Representation ℂ Group Vector where
  toFun g := Matrix.toLin' g.val
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

abbrev scalar : Representation ℂ Plane ℂ := trivial ℂ Plane ℂ

def block (i : Fin 3) :
    (SL2SymmetricEmbeddings.Doublet × ℂ) ≃ₗ[ℂ] Vector where
  toFun x := match i with
    | 0 => ![x.1 0,x.1 1,x.2]
    | 1 => ![x.1 0,x.2,x.1 1]
    | 2 => ![x.2,x.1 0,x.1 1]
  invFun v := match i with
    | 0 => (![v 0,v 1],v 2)
    | 1 => (![v 0,v 2],v 1)
    | 2 => (![v 1,v 2],v 0)
  left_inv x := by
    fin_cases i <;> apply Prod.ext
    all_goals first | rfl | (funext j; fin_cases j <;> rfl)
  right_inv v := by fin_cases i <;> funext j <;> fin_cases j <;> rfl
  map_add' x y := by fin_cases i <;> funext j <;> fin_cases j <;> rfl
  map_smul' c x := by fin_cases i <;> funext j <;> fin_cases j <;> rfl

def planeEquiv (i : Fin 3) : Representation.Equiv
    (SL2SymmetricEmbeddings.doublet.prod scalar) (standard.comp (embedding i)) where
  toLinearEquiv := block i
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change block i (SL2SymmetricEmbeddings.doublet g x.1,x.2) =
      (planeMatrix i g).mulVec (block i x)
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [block,SL2SymmetricEmbeddings.doublet,
        planeMatrix,Matrix.toLin'_apply,Matrix.mulVec,
        dotProduct,Fin.sum_univ_succ]

theorem standard_spanned (i : Fin 3) : Spanned (standard.comp (embedding i)) :=
  SL2SpannedProducts.transport (planeEquiv i)
    (SL2SpannedProducts.prod _ _ SL2SymmetricSpan.standard SL2SymmetricSpan.trivial)

theorem scalar_dual : scalar.dual = trivial ℂ Plane (Module.Dual ℂ ℂ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  rfl

theorem dual_spanned (i : Fin 3) : Spanned (standard.dual.comp (embedding i)) := by
  rw [SplitRepresentationProjection.dual_comp]
  apply SL2SpannedProducts.transport (SplitRepresentationProjection.dualEquiv (planeEquiv i))
  apply SL2SpannedProducts.transport (SplitRepresentationProjection.dualProdEquiv _ _)
  apply SL2SpannedProducts.prod
  · exact SL2SpannedProducts.dualDoublet
  · rw [scalar_dual]
    exact SL2SymmetricSpan.trivial

theorem coefficient_fixed_of_compact {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ Group V)
    (hr : ∀ i, Spanned (rho.comp (embedding i))) (f : Module.Dual ℂ V)
    (hc : ∀ u x, f (rho (compactInclusion u) x) = f x) :
    ∀ g x, f (rho g x) = f x := by
  apply SL3ColorPlanes.invariant rho f
  intro i
  apply SL2SymmetricSpan.coefficient_fixed_of_compact (rho.comp (embedding i)) (hr i) f
  intro u x
  change f (rho (embedding i (SL2SymmetricEmbeddings.compactInclusion u)) x) = f x
  rw [compact_square]
  exact hc _ x

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

abbrev MixedCarrier (a b : ℕ) :=
  (⨂[ℂ]^a Vector) ⊗[ℂ] (⨂[ℂ]^b (Module.Dual ℂ Vector))
@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance

abbrev mixed (a b : ℕ) : Representation ℂ Group (MixedCarrier a b) :=
  (standard.tensorPower a).tprod (standard.dual.tensorPower b)

theorem power_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ Group V) (n : ℕ) (i : Fin 3) :
    (rho.tensorPower n).comp (embedding i) =
      SL2SymmetricSpan.power (rho.comp (embedding i)) n := rfl

theorem mixed_spanned (a b : ℕ) (i : Fin 3) : Spanned ((mixed a b).comp (embedding i)) := by
  change Spanned ((SL2SymmetricSpan.power (standard.comp (embedding i)) a).tprod
    (SL2SymmetricSpan.power (standard.dual.comp (embedding i)) b))
  exact SL2SymmetricSpan.tensor _ _
    (SL2SymmetricSpan.tensorPower _ (standard_spanned i) a)
    (SL2SymmetricSpan.tensorPower _ (dual_spanned i) b)

theorem standard_compact : standard.comp compactInclusion = SU3DefiningExterior.rho := rfl

theorem tensorPower_compact {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ Group V) (n : ℕ) :
    (rho.tensorPower n).comp compactInclusion =
      Representation.tensorPower (rho.comp compactInclusion) n := rfl

theorem mixed_compact (a b : ℕ) :
    (mixed a b).comp compactInclusion = SU3TensorPositive.mixed a b := by
  change Representation.tprod ((standard.tensorPower a).comp compactInclusion)
      ((standard.dual.tensorPower b).comp compactInclusion) = _
  rw [tensorPower_compact,tensorPower_compact,
    SplitRepresentationProjection.dual_comp,standard_compact]

/-- Every compact invariant on the actual raw mixed source extends to SL(3). -/
theorem mixed_invariant (a b : ℕ) (f : Module.Dual ℂ (MixedCarrier a b))
    (hc : ∀ u x, f (SU3TensorPositive.mixed a b u x) = f x) :
    ∀ g x, f (mixed a b g x) = f x := by
  apply coefficient_fixed_of_compact _ (mixed_spanned a b) f
  intro u x
  have he := congrArg (fun r => r u) (mixed_compact a b)
  exact he ▸ hc u x

end
end Math.SL3CompactComparison
