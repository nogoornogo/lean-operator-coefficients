import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourUpper
import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWaves
import Physics.FieldTheory.Jets.LorentzRankFour.Core.Invariant
import Math.Algebra.Waves.ScalarFourWaveCubature

/-! Complete admitted invariant coefficients at four fields/four derivatives. -/
namespace Physics.ScalarQuarticFourCompleteness
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM ScalarQuarticFourTensors
open FourWaveEvaluation FourWavePolarization LorentzFiniteControls

def momenta (a : Fin 36) (s i : Fin 4) : ℂ := ScalarFourWaveCubature.raw a s i

theorem conservation (a : Fin 36) (i : Fin 4) : ∑ s : Fin 4, momenta a s i = 0 := by
  have he := congrArg GaussianInt.toComplex (ScalarFourWaveCubature.conservation a i)
  simpa only [map_sum,map_zero,momenta] using he

theorem null (a : Fin 36) (s : Fin 4) :
    (momenta a s 0)^2-(momenta a s 1)^2-(momenta a s 2)^2-(momenta a s 3)^2 = 0 := by
  have he := congrArg GaussianInt.toComplex (ScalarFourWaveCubature.null a s)
  simpa only [map_sub,map_pow,map_zero,momenta] using he

def functional : OffShell →ₗ[ℂ] ℂ := (1/27648 : ℂ) • ∑ a : Fin 36, onJets (momenta a)

theorem annihilates : P.relations ≤ functional.ker := by
  intro p hp
  change (1/27648 : ℂ) • (∑ a : Fin 36, onJets (momenta a)) p = 0
  rw [LinearMap.sum_apply]
  have he : ∀ a : Fin 36, onJets (momenta a) p = 0 := fun a =>
    ScalarQuarticFourWaves.annihilates (momenta a) (conservation a) (null a) hp
  simp only [he,Finset.sum_const_zero,smul_zero]

theorem basis_value (r : Fin 5) (i j k l : Fin 4) :
    functional (word r (E i) (E j) (E k) (E l)) =
      (1/27648 : ℂ)*GaussianInt.toComplex (ScalarFourWaveCubature.expected r i j k l) := by
  have he : (∑ a : Fin 36, moment (momenta a) r i j k l) =
      GaussianInt.toComplex (ScalarFourWaveCubature.sumMoment r i j k l) := by
    rw [ScalarFourWaveCubature.sumMoment,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact (map_moment GaussianInt.toComplex (ScalarFourWaveCubature.raw a) r i j k l).symm
  change (1/27648 : ℂ) • (∑ a : Fin 36, onJets (momenta a)) (word r (E i) (E j) (E k) (E l)) = _
  simp only [LinearMap.sum_apply,ScalarQuarticFourWaves.word_value,smul_eq_mul]
  rw [he,ScalarFourWaveCubature.moments]

theorem cast_metric (i j : Fin 4) :
    GaussianInt.toComplex (ScalarFourWaveCubature.metric i j) = LorentzRankFour.metric i j := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · subst i; norm_num [ScalarFourWaveCubature.metric,LorentzRankFour.metric]
    · fin_cases i <;> simp_all [ScalarFourWaveCubature.metric,LorentzRankFour.metric]
  · simp [ScalarFourWaveCubature.metric,LorentzRankFour.metric,hij]

def alpha (r : Fin 5) : ℂ := (ScalarFourWaveCubature.alpha r : ℂ)/27648
def beta (r : Fin 5) : ℂ := (ScalarFourWaveCubature.beta r : ℂ)/27648

theorem basis_formula (r : Fin 5) (i j k l : Fin 4) :
    tensor functional r (E i) (E j) (E k) (E l) =
      alpha r*LorentzRankFour.metric i j*LorentzRankFour.metric k l+
      beta r*(LorentzRankFour.metric i k*LorentzRankFour.metric j l+
        LorentzRankFour.metric i l*LorentzRankFour.metric j k) := by
  rw [tensor_apply,basis_value]
  simp only [ScalarFourWaveCubature.expected,map_add,map_mul,map_intCast,cast_metric,alpha,beta]
  ring

theorem invariant_word (g : LorentzDirections.Group) (r : Fin 5) (u v w x : Dir) :
    functional (word r (LorentzDirections.direction g u) (LorentzDirections.direction g v)
      (LorentzDirections.direction g w) (LorentzDirections.direction g x)) = functional (word r u v w x) :=
  LorentzRankFour.invariant_of_components (tensor functional r) (alpha r) (beta r)
    (basis_formula r) g u v w x

theorem invariant (g : LorentzDirections.Group) (p : V) : functional (offAction g p.val) = functional p.val := by
  have hp : p.val ∈ ScalarQuarticFourSource.wordSpan := by
    rw [← ScalarQuarticFourSource.grade_eq_span]
    exact p.property
  refine Submodule.span_induction (p := fun p _ => functional (offAction g p) = functional p) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨r,i,j,k,l,rfl⟩
    rw [word_covariant]
    exact invariant_word g r (E i) (E j) (E k) (E l)
  · simp
  · intro p q _ _ hp hq
    simp only [map_add,hp,hq]
  · intro c p _ hp
    simp only [map_smul,hp]

theorem normalization : functional ScalarQuarticContractions.C4 = 1 := by
  rw [ScalarQuarticFourUpper.C_word,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,← tensor_apply,basis_formula]
  norm_num [alpha,beta,ScalarFourWaveCubature.alpha,ScalarFourWaveCubature.beta,
    LorentzRankFour.metric,ScalarQuarticContractions.eta,Fin.sum_univ_succ]

def normalized : selected.Coefficient := ⟨{
  toLinearMap := functional.comp V.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro p
    exact invariant g p }, fun _ hp => annihilates hp⟩

theorem normalized_value : ScalarQuarticFourUpper.evaluate normalized = 1 := normalization

def equivalence : selected.Coefficient ≃ₗ[ℂ] ℂ where
  toLinearMap := ScalarQuarticFourUpper.evaluate
  invFun c := c • normalized
  left_inv F := ScalarQuarticFourUpper.evaluate_injective (by
    change ScalarQuarticFourUpper.evaluate (ScalarQuarticFourUpper.evaluate F • normalized) = _
    rw [map_smul,normalized_value,smul_eq_mul,mul_one])
  right_inv c := by
    change ScalarQuarticFourUpper.evaluate (c • normalized) = c
    rw [map_smul,normalized_value,smul_eq_mul,mul_one]

@[simp] theorem extraction (F : selected.Coefficient) :
    equivalence F = F.val ScalarQuarticFourUpper.generator := rfl

@[simp] theorem reconstruction (F : selected.Coefficient) :
    (equivalence F) • normalized = F := equivalence.symm_apply_apply F

@[simp] theorem arbitrary_value (c : ℂ) :
    (c • normalized).val ScalarQuarticFourUpper.generator = c := equivalence.apply_symm_apply c

theorem coefficient_dimension : Module.finrank ℂ selected.Coefficient = 1 := by
  rw [equivalence.finrank_eq]
  exact Module.finrank_self ℂ

theorem normalized_nonzero : normalized ≠ 0 := by
  intro h
  have he := normalized_value
  rw [h,map_zero] at he
  exact zero_ne_one he

end
end Physics.ScalarQuarticFourCompleteness
