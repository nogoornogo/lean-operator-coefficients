import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInput
import Math.Algebra.Constructions.ColoredQuarticSource

/-! Actual colored source tensors; the all-first-derivative tensor is not
assumed pair symmetric. -/
namespace Physics.HiggsQuarticFourTensors
set_option autoImplicit false
noncomputable section
open Math ColoredQuarticWords
open DerivativeLiteratureHiggs (Label)
abbrev A := DerivativeLiteratureHiggs.A
abbrev V := HiggsQuarticFourInput.V
abbrev transport := HiggsLagrangianInput.transport

theorem field_eq (s : Label) : field s = DerivativeLiteratureHiggs.h s.1 s.2 := by
  cases s
  rfl

theorem field_invariant (g : LorentzDirections.Group) (s : Label) :
    transport g (field s) = field s :=
  HiggsLagrangianInput.field_invariant g s.1 s.2

theorem dirD_covariant (g : LorentzDirections.Group) (u : Dir) (p : A) :
    transport g (dirD u p) = dirD (LorentzDirections.direction g u) (transport g p) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [map_add,hu,hv]
  | single i c =>
    have he : Finsupp.single i c = c • Finsupp.single i (1 : ℂ) := by simp
    simp only [he,map_smul,Derivation.smul_apply,dirD_single,one_smul]
    congr 1
    rw [dirD_apply]
    exact HiggsLagrangianInput.covariance g i p

theorem j1_covariant (g : LorentzDirections.Group) (s : Label) (u : Dir) :
    transport g (j1 s u) = j1 s (LorentzDirections.direction g u) := by
  simp only [j1,dirD_covariant,field_invariant]
theorem j2_covariant (g : LorentzDirections.Group) (s : Label) (u v : Dir) :
    transport g (j2 s u v) = j2 s (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) := by
  simp only [j2,dirD_covariant,j1_covariant]
theorem j3_covariant (g : LorentzDirections.Group) (s : Label) (u v w : Dir) :
    transport g (j3 s u v w) = j3 s (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) (LorentzDirections.direction g w) := by
  simp only [j3,dirD_covariant,j2_covariant]
theorem j4_covariant (g : LorentzDirections.Group) (s : Label) (u v w x : Dir) :
    transport g (j4 s u v w x) = j4 s (LorentzDirections.direction g u)
      (LorentzDirections.direction g v) (LorentzDirections.direction g w)
      (LorentzDirections.direction g x) := by
  simp only [j4,dirD_covariant,j3_covariant]

theorem word_covariant (a : Fin 4 → Label) (r : Fin 5) (g : LorentzDirections.Group)
    (u v w x : Dir) : transport g (word a r u v w x) =
      word a r (LorentzDirections.direction g u) (LorentzDirections.direction g v)
        (LorentzDirections.direction g w) (LorentzDirections.direction g x) := by
  fin_cases r <;> simp only [word,map_mul,field_invariant,
    j1_covariant,j2_covariant,j3_covariant,j4_covariant]

theorem tensor_invariant (f : A →ₗ[ℂ] ℂ)
    (hInv : ∀ g p, p ∈ V → f (transport g p) = f p)
    (a : Fin 4 → Label) (r : Fin 5) : ∀ g u v w x,
      tensor f a r (LorentzDirections.direction g u) (LorentzDirections.direction g v)
        (LorentzDirections.direction g w) (LorentzDirections.direction g x) =
      tensor f a r u v w x := by
  intro g u v w x
  simpa only [tensor_apply,word_covariant] using
    hInv g (word a r u v w x) (word_grade a r u v w x)

theorem tensor_symmetric (f : A →ₗ[ℂ] ℂ) (a : Fin 4 → Label) (r : Fin 4) :
    ∀ u v w x, tensor f a r.castSucc u v w x = tensor f a r.castSucc v u w x := by
  intro u v w x
  exact congrArg f (word_symmetric a r u v w x)

end
end Physics.HiggsQuarticFourTensors
