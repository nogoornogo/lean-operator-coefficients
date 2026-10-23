import Math.RepresentationTheory.Relations.FiniteStatisticalFactor
import Math.RepresentationTheory.Relations.CommutingStatisticsModule

/-! The independently computed local exchange matrices define a genuine
statistics action on flavor inputs, compatible with residual symmetry. -/
namespace Math.FiniteLocalStatistics
set_option autoImplicit false
noncomputable section
open Representation
variable {G H S A X I : Type*} [Group G] [Group H] [Group S]
  [Fintype I] [DecidableEq I] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ i, f (v i) • p i)
  (ell : Representation ℂ S A) (flavor : Representation ℂ S X)
  (lc : ∀ s g u, ell s (a g u) = a g (ell s u))
  (fc : ∀ s h u, flavor s (x h u) = x h (flavor s u))

def localMap (s : S) : IntertwiningMap a a where
  toLinearMap := ell s
  isIntertwining' g := by ext u; exact lc s g u

def localEquiv (s : S) : Representation.Equiv a a where
  toLinearEquiv := LinearEquiv.ofBijective (ell s) (Representation.apply_bijective ell s)
  isIntertwining' g := by ext u; exact lc s g u

def flavorEquiv (s : S) : Representation.Equiv x x where
  toLinearEquiv := LinearEquiv.ofBijective (flavor s) (Representation.apply_bijective flavor s)
  isIntertwining' h := by ext u; exact fc s h u

def matrix (s : S) (i m : I) : ℂ := p m (ell s (v i))

omit [Fintype I] [DecidableEq I] in
theorem matrix_agrees (s : S) (i m : I) :
    matrix a p v ell s i m =
      FiniteStatisticalFactor.matrix a p v (localEquiv a ell lc) s i m := rfl

include hv in
omit [Fintype I] in
theorem matrix_one (i m : I) : matrix a p v ell 1 i m = if m = i then 1 else 0 := by
  simpa [matrix] using hv m i

include hp lc in
omit [DecidableEq I] in
theorem matrix_mul (s t : S) (i n : I) :
    matrix a p v ell (s * t) i n = ∑ m, matrix a p v ell t i m * matrix a p v ell s m n := by
  have h := congrArg (fun f : IntertwiningMap a (Representation.trivial ℂ G ℂ) =>
    f (ell t (v i))) (hp ((p n).comp (localMap a ell lc s)))
  simpa [matrix, localMap, IntertwiningMap.sum_apply, map_mul,
    Module.End.mul_apply, mul_comm] using h

def inputMap (s : S) : (I →₀ X) →ₗ[ℂ] (I →₀ X) :=
  Finsupp.lsum ℂ (fun i => ∑ m, matrix a p v ell s i m •
    ((Finsupp.lsingle m).comp (flavor s)))

omit [DecidableEq I] in
@[simp] theorem inputMap_single (s : S) (i : I) (u : X) :
    inputMap a p v ell flavor s (Finsupp.single i u) =
      ∑ m, Finsupp.single m (matrix a p v ell s i m • flavor s u) := by
  simp [inputMap]

include hv hp lc in
def statistics : Representation ℂ S (I →₀ X) where
  toFun := inputMap a p v ell flavor
  map_one' := by
    apply Finsupp.lhom_ext
    intro i u
    rw [inputMap_single]
    simp only [matrix_one a p v hv ell, map_one, Module.End.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro m _ hm
      simp [hm]
    · simp
  map_mul' s t := by
    apply Finsupp.lhom_ext
    intro i u
    simp only [Module.End.mul_apply, inputMap_single, map_sum, map_smul]
    simp only [smul_smul]
    rw [Finset.sum_comm]
    simp only [matrix_mul a p v hp ell lc, map_mul, Module.End.mul_apply,
      Finset.sum_smul, mul_comm]
    apply Finset.sum_congr rfl
    intro n _
    exact map_sum (Finsupp.singleAddHom n) _ _

include fc in
omit [DecidableEq I] in
theorem commutes (s : S) (h : H) (u : I →₀ X) :
    inputMap a p v ell flavor s ((x.finsupp I) h u) =
      (x.finsupp I) h (inputMap a p v ell flavor s u) := by
  have he : inputMap a p v ell flavor s ∘ₗ (x.finsupp I) h =
      (x.finsupp I) h ∘ₗ inputMap a p v ell flavor s := by
    apply Finsupp.lhom_ext
    intro i u
    simp [fc s h, map_sum, map_smul]
  exact LinearMap.congr_fun he u

def inputExchange (s : S) : IntertwiningMap (x.finsupp I) (x.finsupp I) where
  toLinearMap := inputMap a p v ell flavor s
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    exact commutes a x p v ell flavor fc s h u

end
end Math.FiniteLocalStatistics
