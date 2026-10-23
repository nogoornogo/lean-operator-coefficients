import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentBasis
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourUpper
import Physics.FieldTheory.Jets.LorentzRankFour.Core.ThreeInvariant
import Math.Algebra.HiggsFourWaveCubature.Contractions

/-! A finite ordered-moment certificate implies actual full-group invariance.
The concrete certificates are discharged in the final coefficient module. -/
namespace Physics.HiggsQuarticFourMomentInvariance
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourMomentBasis
open ColoredQuarticWords (word E)
open ColoredFourWavePolarization (assignments orders)

abbrev Moments (r : Fin 3) : Prop := ∀ s t u v i j k l : Fin 4,
  HiggsFourWaveCubature.sumMoment r s t u v i j k l =
    HiggsFourWaveCubature.expected r s t u v i j k l

def channel (r : Fin 3) (t : Fin 5) (p : Fin 24) (c : Fin 3) : ℂ :=
  GaussianInt.toComplex (HiggsFourWaveCubature.channel r
    (assignments p (orders t 0)) (assignments p (orders t 1))
    (assignments p (orders t 2)) (assignments p (orders t 3)) c)
def coordinate (r : Fin 3) (a : Fin 4 → Label) (t : Fin 5) (c : Fin 3) : ℂ :=
  scale r*∑ p : Fin 24, ColoredWavePairing.tensor p (fun n => Finsupp.single (a n) 1)*channel r t p c

theorem cast_metric (i j : Fin 4) :
    GaussianInt.toComplex (HiggsFourWaveCubature.metric i j) = LorentzRankFour.metric i j := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [HiggsFourWaveCubature.metric,LorentzRankFour.metric]

theorem expected_value (r : Fin 3) (t : Fin 5) (p : Fin 24) (i j k l : Fin 4) :
    GaussianInt.toComplex (HiggsFourWaveCubature.expected r
      (assignments p (orders t 0)) (assignments p (orders t 1))
      (assignments p (orders t 2)) (assignments p (orders t 3)) i j k l) =
      channel r t p 0*LorentzRankFour.metric i j*LorentzRankFour.metric k l+
      channel r t p 1*LorentzRankFour.metric i k*LorentzRankFour.metric j l+
      channel r t p 2*LorentzRankFour.metric i l*LorentzRankFour.metric j k := by
  simp only [HiggsFourWaveCubature.expected_channels,map_add,map_mul,cast_metric,channel]

theorem basis_formula (r : Fin 3) (hM : Moments r) (a : Fin 4 → Label) (t : Fin 5)
    (i j k l : Fin 4) : functional r (word a t (E i) (E j) (E k) (E l)) =
      coordinate r a t 0*LorentzRankFour.metric i j*LorentzRankFour.metric k l+
      coordinate r a t 1*LorentzRankFour.metric i k*LorentzRankFour.metric j l+
      coordinate r a t 2*LorentzRankFour.metric i l*LorentzRankFour.metric j k := by
  rw [word_value]
  simp only [hM,expected_value,coordinate,Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem lorentz_word (r : Fin 3) (hM : Moments r) (g : LorentzDirections.Group)
    (a : Fin 4 → Label) (t : Fin 5) (i j k l : Fin 4) :
    functional r (HiggsLagrangianInput.transport g (word a t (E i) (E j) (E k) (E l))) =
      functional r (word a t (E i) (E j) (E k) (E l)) := by
  have hc : ∀ i j k l : Fin 4,
      ColoredQuarticWords.tensor (functional r) a t
        (LorentzFiniteControls.E i) (LorentzFiniteControls.E j)
        (LorentzFiniteControls.E k) (LorentzFiniteControls.E l) =
      coordinate r a t 0*LorentzRankFour.metric i j*LorentzRankFour.metric k l+
      coordinate r a t 1*LorentzRankFour.metric i k*LorentzRankFour.metric j l+
      coordinate r a t 2*LorentzRankFour.metric i l*LorentzRankFour.metric j k := by
    intro i j k l
    exact basis_formula r hM a t i j k l
  have hi := LorentzRankFourThree.invariant_of_components
    (ColoredQuarticWords.tensor (functional r) a t)
    (coordinate r a t 0) (coordinate r a t 1) (coordinate r a t 2) hc g (E i) (E j) (E k) (E l)
  exact (congrArg (functional r) (HiggsQuarticFourTensors.word_covariant a t g
    (E i) (E j) (E k) (E l))).trans hi

theorem lorentz (r : Fin 3) (hM : Moments r) (g : LorentzDirections.Group)
    (p : HiggsQuarticFourInput.V) : functional r (HiggsLagrangianInput.transport g p.val) =
      functional r p.val := by
  have hp : p.val ∈ ColoredQuarticSource.wordSpan Label := by
    rw [← ColoredQuarticSource.grade_eq_span]
    exact p.property
  refine Submodule.span_induction (p := fun p _ =>
    functional r (HiggsLagrangianInput.transport g p) = functional r p) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨a,t,i,j,k,l,rfl⟩
    exact lorentz_word r hM g a t i j k l
  · simp
  · intro p q _ _ hp hq; simp only [map_add,hp,hq]
  · intro c p _ hp; simp only [map_smul,hp]

theorem invariant (r : Fin 3) (hM : Moments r) (g : HiggsStandardInput.Group)
    (p : HiggsQuarticFourInput.V) :
    functional r (HiggsStandardInput.transport g p.val) = functional r p.val := by
  have hq : HiggsLagrangianInput.transport g.2 p.val ∈ HiggsQuarticFourInput.V := by
    have hp := HiggsQuarticFourInput.stable (1,g.2) p.property
    change HiggsStandardInput.transport (1,g.2) p.val ∈ HiggsQuarticFourInput.V at hp
    simpa only [HiggsQuarticFourUpper.lorentz_only] using hp
  calc
    _ = functional r (HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g.1
        (HiggsLagrangianInput.transport g.2 p.val)) := congrArg (functional r) (HiggsStandardInput.factorize g p.val)
    _ = functional r (HiggsLagrangianInput.transport g.2 p.val) := internal r g.1 ⟨_,hq⟩
    _ = _ := lorentz r hM g.2 p

def coefficient (r : Fin 3) (hM : Moments r) : HiggsQuarticFourInput.selected.Coefficient := ⟨{
  toLinearMap := (functional r).comp HiggsQuarticFourInput.V.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro p
    exact invariant r hM g p }, fun _ hp => annihilates r hp⟩

theorem coefficient_apply (r : Fin 3) (hM : Moments r) (p : HiggsQuarticFourInput.V) :
    (coefficient r hM).val p = functional r p.val := rfl

end
end Physics.HiggsQuarticFourMomentInvariance
