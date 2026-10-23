import Math.Algebra.Variational.EulerNaturality
import Math.RepresentationTheory.Jets.JetFunctor

/-! Canonical parity-preserving substitutions from separate odd/even jet maps. -/
namespace Math.LocalPolynomial.BlockJetSubstitution
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {F B I : Type*}
@[reducible] local instance blockAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance blockModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance blockRing : Ring (A F B I) := inferInstance

def oddIn : JetLinear.Jet F I →ₗ[ℂ] JetSpace F B I :=
  Finsupp.lmapDomain ℂ ℂ (fun j => (Sum.inl j.1,j.2))
def evenIn : JetLinear.Jet B I →ₗ[ℂ] JetSpace F B I :=
  Finsupp.lmapDomain ℂ ℂ (fun j => (Sum.inr j.1,j.2))

@[simp] theorem oddIn_single (j : ScalarJetAlgebra.Index F I) (c : ℂ) :
    oddIn (B := B) (Finsupp.single j c) = Finsupp.single (.inl j.1,j.2) c := by simp [oddIn]
@[simp] theorem evenIn_single (j : ScalarJetAlgebra.Index B I) (c : ℂ) :
    evenIn (F := F) (Finsupp.single j c) = Finsupp.single (.inr j.1,j.2) c := by simp [evenIn]

@[simp] theorem oddIn_apply_odd (v : JetLinear.Jet F I) (f : F) (a : I →₀ ℕ) :
    oddIn (B := B) v (.inl f,a) = v (f,a) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  | single j c => obtain ⟨g,b⟩ := j; simp [Finsupp.single_apply,Prod.ext_iff]
@[simp] theorem oddIn_apply_even (v : JetLinear.Jet F I) (b : B) (a : I →₀ ℕ) :
    oddIn v (.inr b,a) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv,hw]
  | single j c => simp [Prod.ext_iff]
@[simp] theorem evenIn_apply_even (v : JetLinear.Jet B I) (b : B) (a : I →₀ ℕ) :
    evenIn (F := F) v (.inr b,a) = v (b,a) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  | single j c => obtain ⟨g,c'⟩ := j; simp [Finsupp.single_apply,Prod.ext_iff]
@[simp] theorem evenIn_apply_odd (v : JetLinear.Jet B I) (f : F) (a : I →₀ ℕ) :
    evenIn v (.inl f,a) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv,hw]
  | single j c => simp [Prod.ext_iff]

@[simp] theorem jetVector_oddIn (v : JetLinear.Jet F I) :
    jetVector (oddIn (B := B) v) = JetFunctor.oddVector v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c => simp [generator]
@[simp] theorem jetVector_evenIn (v : JetLinear.Jet B I) :
    jetVector (evenIn (F := F) v) = JetFunctor.evenVector v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c => simp [generator]

def jets (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) : JetSpace F B I →ₗ[ℂ] JetSpace F B I :=
  Finsupp.linearCombination ℂ (fun j => match j.1 with
    | .inl f => oddIn (L (Finsupp.single (f,j.2) 1))
    | .inr b => evenIn (M (Finsupp.single (b,j.2) 1)))

@[simp] theorem jets_odd (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) (f : F) (a : I →₀ ℕ) :
    jets L M (Finsupp.single (.inl f,a) 1) = oddIn (L (Finsupp.single (f,a) 1)) := by simp [jets]
@[simp] theorem jets_even (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) (b : B) (a : I →₀ ℕ) :
    jets L M (Finsupp.single (.inr b,a) 1) = evenIn (M (Finsupp.single (b,a) 1)) := by simp [jets]

theorem exterior_involute (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (x : MixedJetAlgebra.Odd F I) :
    ExteriorAlgebra.map L (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (ExteriorAlgebra.map L x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | ι_mul v x hx => simp [map_mul,ExteriorAlgebra.map_apply_ι,hx]

def algebra (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) : A F B I →ₐ[ℂ] A F B I :=
  Algebra.TensorProduct.map (ExteriorAlgebra.map L) (JetFunctor.polynomialMap M)

theorem algebra_involute (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) (p : A F B I) :
    algebra L M (MixedJetParity.involute p) = MixedJetParity.involute (algebra L M p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add,hp,hq]
  | tmul x y => simp [algebra,MixedJetParity.involute_tmul,exterior_involute]

/-- No parity or gradient certificate is required from the caller. -/
def substitution (L : JetLinear.Jet F I →ₗ[ℂ] JetLinear.Jet F I)
    (M : JetLinear.Jet B I →ₗ[ℂ] JetLinear.Jet B I) : LinearSubstitution F B I where
  algebra := algebra L M
  jets := jets L M
  generator_map := by
    rintro ⟨s,a⟩
    cases s with
    | inl f => simp [generator,algebra,MixedJetAlgebra.odd,JetFunctor.oddVector]
    | inr b => simp [generator,algebra,MixedJetAlgebra.even,JetFunctor.evenVector,
        JetFunctor.polynomialMap_X]
  twist_map := by intro s p; cases s; exact algebra_involute L M p; rfl
  parity := by
    rintro ⟨s,a⟩ ⟨t,b⟩ h p
    cases s <;> cases t <;> simp_all [twist]

end
end Math.LocalPolynomial.BlockJetSubstitution
