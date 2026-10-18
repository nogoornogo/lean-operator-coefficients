import Math.LieGroups.SpecialUnitary.PlaneGenerationThree
import Math.LieGroups.SpecialUnitary.TwoCircleGeneration
import Math.LieGroups.SpecialUnitary.Block

/-! Three explicit embedded SU(2) planes supply six fixed circle families for actual SU(3). -/
namespace Math.ColorPlaneCircles
set_option autoImplicit false
noncomputable section
open Matrix Representation
abbrev SU3 := SU3PlaneGeneration.SU3
abbrev SU2 := TwoCircleGeneration.SU2

def frame02 : SU3 := ⟨!![-1,0,0; 0,0,-1; 0,-1,0], by
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  · norm_num [Matrix.det_fin_three]⟩
def frame12 : SU3 := ⟨!![0,0,1; 1,0,0; 0,1,0], by
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  · norm_num [Matrix.det_fin_three]⟩

def frame : Fin 3 → SU3 := ![1,frame02,frame12]
def embedding (i : Fin 3) : SU2 →* SU3 :=
  (MulAut.conj (frame i)).toMonoidHom.comp (SUN.Block.inclusion 2 1)

def planeMatrix (i : Fin 3) (u : SU2) : Matrix (Fin 3) (Fin 3) ℂ := match i with
  | 0 => !![u.val 0 0,u.val 0 1,0; u.val 1 0,u.val 1 1,0; 0,0,1]
  | 1 => !![u.val 0 0,0,u.val 0 1; 0,1,0; u.val 1 0,0,u.val 1 1]
  | 2 => !![1,0,0; 0,u.val 0 0,u.val 0 1; 0,u.val 1 0,u.val 1 1]

theorem block_matrix (u : SU2) : (SUN.Block.inclusion 2 1 u).val = planeMatrix 0 u := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem embedding_matrix (i : Fin 3) (u : SU2) : (embedding i u).val = planeMatrix i u := by
  change (frame i).val * (SUN.Block.inclusion 2 1 u).val * star (frame i).val = _
  rw [block_matrix]
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [frame,frame02,frame12,planeMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_apply,Matrix.one_apply]

def form (a b : ℂ) (h : a*star a+b*star b=1) : SU2 :=
  ⟨!![a,b; -star b,star a], by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply] <;>
        first | (solve | ring) | (solve | simpa [Complex.star_def,mul_comm,add_comm] using h)
    · simp [Matrix.det_fin_two] at h ⊢
      exact h⟩

theorem rotation01_eq (a b : ℂ) (h) : SU3PlaneGeneration.rotation01 a b h = embedding 0 (form a b h) := by
  apply Subtype.ext
  rw [embedding_matrix]
  rfl

theorem rotation02_eq (a b : ℂ) (h) : SU3PlaneGeneration.rotation02 a b h = embedding 1 (form a b h) := by
  apply Subtype.ext
  rw [embedding_matrix]
  rfl

def tail (g : SU3) (hv : ∀ j, g.val j 0 = if j=0 then 1 else 0) : SU2 :=
  ⟨SU3PlaneGeneration.tailMatrix g, SU3PlaneGeneration.tail_mem g hv⟩

theorem tail_eq (g : SU3) (hv : ∀ j, g.val j 0 = if j=0 then 1 else 0) :
    g = embedding 2 (tail g hv) := by
  have hr := SU3PlaneGeneration.row_fixed g 0 hv
  apply Subtype.ext
  rw [embedding_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMatrix,tail,SU3PlaneGeneration.tailMatrix,hv,hr]

/-- Invariance on the three actual embedded groups exhausts color invariance. -/
theorem invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) (f : Module.Dual ℂ V)
    (hf : ∀ i u x, f (rho (embedding i u) x) = f x) : ∀ g x, f (rho g x)=f x := by
  intro g x
  obtain ⟨a,b,hn,hz⟩ := SU3PlaneGeneration.eliminate_pair (g.val 0 0) (g.val 1 0)
  let p := SU3PlaneGeneration.rotation01 a b hn
  let u := p*g
  have hu1 : u.val 1 0 = 0 := by
    change (SU3PlaneGeneration.matrix01 a b * g.val) 1 0 = 0
    simpa [SU3PlaneGeneration.matrix01,Matrix.mul_apply,Fin.sum_univ_succ] using hz
  have hu : star (u.val 0 0)*u.val 0 0 + star (u.val 2 0)*u.val 2 0 = 1 := by
    simpa [hu1] using SU3PlaneGeneration.column_norm u
  let q := SU3PlaneGeneration.rotation02 (star (u.val 0 0)) (star (u.val 2 0)) (by simpa using hu)
  have hv : ∀ j : Fin 3, (q*u).val j 0 = if j=0 then 1 else 0 := by
    intro j
    change (SU3PlaneGeneration.matrix02 (star (u.val 0 0)) (star (u.val 2 0)) * u.val) j 0 = _
    fin_cases j
    · simpa [SU3PlaneGeneration.matrix02,Matrix.mul_apply,Fin.sum_univ_succ] using hu
    · simp [SU3PlaneGeneration.matrix02,Matrix.mul_apply,Fin.sum_univ_succ,hu1]
    · simp [SU3PlaneGeneration.matrix02,Matrix.mul_apply,Fin.sum_univ_succ]; ring
  have hp : ∀ x, f (rho p x) = f x := by dsimp only [p]; rw [rotation01_eq]; exact hf 0 _
  have hq : ∀ x, f (rho q x) = f x := by dsimp only [q]; rw [rotation02_eq]; exact hf 1 _
  have hr : ∀ x, f (rho (q*u) x)=f x := by rw [tail_eq (q*u) hv]; exact hf 2 _
  have he := hr x
  change f (rho (q*(p*g)) x)=f x at he
  simp only [map_mul,Module.End.mul_apply,hq,hp] at he
  exact he

def torus : Circle →* SU3 := (embedding 0).comp TauCeti.SU2.torusHom

def tests (i : Fin 3 × Bool) : SU3 := embedding i.1 (TwoCircleGeneration.tests i.2)

theorem embedding_conjugate (i : Fin 3) (u : SU2) :
    embedding i u = frame i * embedding 0 u * (frame i)⁻¹ := by
  simp [embedding,frame,MulAut.conj_apply]

theorem embedding_mix (i : Fin 3) (z : Circle) :
    embedding i (TwoCircleGeneration.mix * TauCeti.SU2.torusHom z * TwoCircleGeneration.mix⁻¹) =
      (frame i * embedding 0 TwoCircleGeneration.mix) * torus z *
        (frame i * embedding 0 TwoCircleGeneration.mix)⁻¹ := by
  rw [embedding_conjugate]
  simp [torus,map_mul,mul_assoc]

theorem exhaustive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) (hi : IntegralTorusTests.Integral rho torus) :
    FiniteInvariantKernel.Exhaustive rho tests := by
  intro f hf
  apply invariant rho f
  intro i
  apply TwoCircleGeneration.invariant (rho.comp (embedding i)) f
  · have hs : ∀ x, f (rho (frame i * torus IntegralTorusTests.sample * (frame i)⁻¹) x) = f x := by
      intro x
      have he := hf (i,false) x
      change f (rho (embedding i (TauCeti.SU2.torusHom IntegralTorusTests.sample)) x) = f x at he
      rw [embedding_conjugate i] at he
      exact he
    have ht := IntegralTorusTests.conjugate_invariant rho torus hi (frame i) f hs
    intro z x
    change f (rho (embedding i (TauCeti.SU2.torusHom z)) x) = f x
    rw [embedding_conjugate i]
    exact ht z x
  · have hs : ∀ x, f (rho ((frame i * embedding 0 TwoCircleGeneration.mix) *
        torus IntegralTorusTests.sample * (frame i * embedding 0 TwoCircleGeneration.mix)⁻¹) x) = f x := by
      intro x
      simpa only [tests,TwoCircleGeneration.tests,↓reduceIte,embedding_mix] using hf (i,true) x
    have ht := IntegralTorusTests.conjugate_invariant rho torus hi
      (frame i * embedding 0 TwoCircleGeneration.mix) f hs
    intro z x
    simpa only [MonoidHom.comp_apply,embedding_mix] using ht z x

end
end Math.ColorPlaneCircles