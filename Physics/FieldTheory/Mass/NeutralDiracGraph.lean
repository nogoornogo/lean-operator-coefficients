import Physics.FieldTheory.Mass.DiracWeylConvention
import Math.LinearAlgebra.NeutralKernelGraph

/-! Exact multi-copy neutral kernel in the symmetric all-left-handed Dirac
convention. Heavy mixing is invertible; no spectrum or kinetic metric supplied. -/
namespace GUT.NeutralDiracGraph
set_option autoImplicit false
noncomputable section
variable {A B C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]

def mixingMap (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) : (A × C) →ₗ[ℂ] B :=
  D.comp (LinearMap.fst ℂ A C)+M.toLinearMap.comp (LinearMap.snd ℂ A C)

theorem kernel_iff (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B)
    (x : (A × C) × Module.Dual ℂ B) :
    x ∈ DiracWeylConvention.radical (mixingMap D M) ↔
      x.1.2 = -M.symm (D x.1.1) ∧ x.2 = 0 := by
  rw [DiracWeylConvention.mem_radical_iff]
  constructor
  · rintro ⟨hx,hphi⟩
    constructor
    · apply M.injective
      change D x.1.1+M x.1.2=0 at hx
      simpa using (eq_neg_of_add_eq_zero_right hx)
    · ext b
      have h := hphi (0,M.symm b)
      simpa [mixingMap] using h
  · rintro ⟨hc,hphi⟩
    constructor
    · simp [mixingMap,hc]
    · simp [hphi]

/-- The symmetric mass is reconstructed by the shared Weyl convention. -/
theorem mass_symmetric (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) :
    (DiracWeylConvention.massBilinear (mixingMap D M)).IsSymm :=
  DiracWeylConvention.massBilinear_isSymm _

def light (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) :
    A →ₗ[ℂ] ((A × C) × Module.Dual ℂ B) where
  toFun a := ((a,-M.symm (D a)),0)
  map_add' a b := by simp [add_comm]
  map_smul' c a := by simp

theorem light_mem (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) (a : A) :
    light D M a ∈ DiracWeylConvention.radical (mixingMap D M) := by
  rw [kernel_iff]
  exact ⟨rfl,rfl⟩

theorem light_coordinates (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B)
    (x : (A × C) × Module.Dual ℂ B)
    (hx : x ∈ DiracWeylConvention.radical (mixingMap D M)) :
    light D M x.1.1 = x := by
  rcases (kernel_iff D M x).mp hx with ⟨hc,hb⟩
  exact Prod.ext (Prod.ext rfl hc.symm) hb.symm

variable {n : ℕ}
def restrict (f : ((A × C) × Module.Dual ℂ B) [⋀^Fin n]→ₗ[ℂ] ℂ)
    (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) := f.compLinearMap (light D M)

theorem restrict_zero_iff (f : ((A × C) × Module.Dual ℂ B) [⋀^Fin n]→ₗ[ℂ] ℂ)
    (D : A →ₗ[ℂ] B) (M : C ≃ₗ[ℂ] B) : restrict f D M = 0 ↔
      ∀ x : Fin n → ((A × C) × Module.Dual ℂ B),
        (∀ i, x i ∈ DiracWeylConvention.radical (mixingMap D M)) → f x = 0 := by
  constructor
  · intro hz x hx
    have he : light D M ∘ (fun i => (x i).1.1) = x := by
      funext i
      exact light_coordinates D M (x i) (hx i)
    have hv := DFunLike.congr_fun hz (fun i => (x i).1.1)
    change f (light D M ∘ (fun i => (x i).1.1)) = 0 at hv
    rw [he] at hv
    exact hv
  · intro hx
    ext a
    exact hx (light D M ∘ a) (fun i => light_mem D M (a i))

end
end GUT.NeutralDiracGraph
