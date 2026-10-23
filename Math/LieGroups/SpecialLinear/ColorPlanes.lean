import Math.LieGroups.SpecialUnitary.ColorPlaneCircles
import Math.RepresentationTheory.SU2.SL2SymmetricEmbeddings
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-! The three complex coordinate planes generate SL(3). Their compact parts
are the actual SU(3) planes used by the color representation. -/
namespace Math.SL3ColorPlanes
set_option autoImplicit false
noncomputable section
open Matrix

abbrev Group := Matrix.SpecialLinearGroup (Fin 3) ℂ
abbrev Plane := SL2SymmetricEmbeddings.Group

def compactInclusion : ColorPlaneCircles.SU3 →* Group where
  toFun g := ⟨g.val, (mem_specialUnitaryGroup_iff.mp g.property).2⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

def planeMatrix (i : Fin 3) (g : Plane) : Matrix (Fin 3) (Fin 3) ℂ := match i with
  | 0 => !![g.val 0 0,g.val 0 1,0; g.val 1 0,g.val 1 1,0; 0,0,1]
  | 1 => !![g.val 0 0,0,g.val 0 1; 0,1,0; g.val 1 0,0,g.val 1 1]
  | 2 => !![1,0,0; 0,g.val 0 0,g.val 0 1; 0,g.val 1 0,g.val 1 1]

theorem plane_det (i : Fin 3) (g : Plane) : (planeMatrix i g).det = 1 := by
  have hg := g.property
  rw [det_fin_two] at hg
  fin_cases i <;> simpa [planeMatrix,det_fin_three] using hg

def embedding (i : Fin 3) : Plane →* Group where
  toFun g := ⟨planeMatrix i g, plane_det i g⟩
  map_one' := by
    apply Subtype.ext
    change planeMatrix i 1 = 1
    fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [planeMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change planeMatrix i (g*h) = planeMatrix i g * planeMatrix i h
    fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [planeMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

theorem compact_square (i : Fin 3) (u : ColorPlaneCircles.SU2) :
    embedding i (SL2SymmetricEmbeddings.compactInclusion u) =
      compactInclusion (ColorPlaneCircles.embedding i u) := by
  apply Subtype.ext
  change planeMatrix i _ = (ColorPlaneCircles.embedding i u).val
  rw [ColorPlaneCircles.embedding_matrix]
  fin_cases i <;> rfl

def coordinates : Fin 3 → Fin 2 → Fin 3 := ![![0,1],![0,2],![1,2]]

theorem coordinates_injective (i : Fin 3) : Function.Injective (coordinates i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [coordinates]

theorem embedding_transvection (i : Fin 3) {a b : Fin 2} (hab : a ≠ b) (c : ℂ) :
    embedding i (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection ((coordinates_injective i).ne hab) c := by
  apply Subtype.ext
  change planeMatrix i (SpecialLinearGroup.transvection hab c) =
    Matrix.transvection (coordinates i a) (coordinates i b) c
  fin_cases i <;> fin_cases a <;> fin_cases b <;> try contradiction
  all_goals
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [planeMatrix,coordinates,SpecialLinearGroup.transvection_coe,
        Matrix.transvection,Matrix.single]

theorem transvection_in_plane (t : Matrix.TransvectionStruct (Fin 3) ℂ) :
    ∃ (i : Fin 3) (g : Plane), embedding i g = t.toSpecialLinearGroup := by
  rcases t with ⟨a,b,hab,c⟩
  fin_cases a <;> fin_cases b <;> try contradiction
  · exact ⟨0,SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c,
      embedding_transvection 0 (by decide) c⟩
  · exact ⟨1,SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c,
      embedding_transvection 1 (by decide) c⟩
  · exact ⟨0,SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c,
      embedding_transvection 0 (by decide) c⟩
  · exact ⟨2,SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c,
      embedding_transvection 2 (by decide) c⟩
  · exact ⟨1,SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c,
      embedding_transvection 1 (by decide) c⟩
  · exact ⟨2,SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c,
      embedding_transvection 2 (by decide) c⟩

theorem closure_planes :
    Subgroup.closure {g : Group | ∃ i u, embedding i u = g} = ⊤ := by
  apply top_unique
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
  apply Subgroup.closure_mono
  rintro g ⟨t,rfl⟩
  exact transvection_in_plane t

/-- No topology or continuity premise is required for the plane-generation step. -/
theorem invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ Group V) (f : Module.Dual ℂ V)
    (hf : ∀ i u x, f (rho (embedding i u) x) = f x) :
    ∀ g x, f (rho g x) = f x := by
  let H : Subgroup Group :=
    { carrier := {g | ∀ x, f (rho g x) = f x}
      one_mem' := by intro x; simp
      mul_mem' := by
        intro g h hg hh x
        change ∀ x, f (rho g x) = f x at hg
        change ∀ x, f (rho h x) = f x at hh
        rw [map_mul,Module.End.mul_apply,hg,hh]
      inv_mem' := by
        intro g hg x
        have he := hg (rho g⁻¹ x)
        simpa only [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,
          Module.End.one_apply] using he.symm }
  have hle : Subgroup.closure {g : Group | ∃ i u, embedding i u = g} ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro g ⟨i,u,rfl⟩
    exact hf i u
  rw [closure_planes] at hle
  intro g
  exact hle (Subgroup.mem_top g)

end
end Math.SL3ColorPlanes
