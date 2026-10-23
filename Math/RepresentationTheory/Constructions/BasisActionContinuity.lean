import Math.RepresentationTheory.Unitary.ContinuousConstructions
import Math.RepresentationTheory.Exterior.PatternExteriorSource
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-! Continuity from finite basis coefficients, including actual statistical
images. No topology on the supplied algebraic carriers is required. -/
namespace Math.BasisActionContinuity
set_option autoImplicit false
noncomputable section
open Representation FiniteBasisHilbertization ContinuousUnitaryConstructions
open scoped TensorProduct
variable {G I J V W : Type*} [Group G] [TopologicalSpace G]
  [Fintype I] [Fintype J] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Coefficients (b : Module.Basis I ℂ V) (rho : Representation ℂ G V) : Prop :=
  ∀ i j, Continuous (fun g => b.repr (rho g (b i)) j)

theorem copy_continuous (b : Module.Basis I ℂ V) (rho : Representation ℂ G V)
    (h : Coefficients b rho) : ContinuousRepresentationScope.IsJointlyContinuous (basisCopyRepresentation b rho) := by
  apply basisCopyRepresentation_jointlyContinuous
  intro i
  let e := Copy.coordinateEquiv b
  have hc : Continuous (fun g => e (⟨rho g (b i)⟩ : Copy b)) :=
    (PiLp.continuous_toLp 2 (fun _ : I => ℂ)).comp (continuous_pi (h i))
  exact (e.symm.toLinearMap.continuous_of_finiteDimensional.comp hc).congr
    (fun g => e.symm_apply_apply _)

omit [Fintype I] in
theorem trivial (b : Module.Basis I ℂ V) : Coefficients b (Representation.trivial ℂ G V) :=
  fun _ _ => by simpa only [Representation.trivial_apply,LinearMap.id_apply] using (continuous_const)

omit [Fintype I] [Fintype J] in
theorem tensor (b : Module.Basis I ℂ V) (d : Module.Basis J ℂ W)
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (hr : Coefficients b rho) (hs : Coefficients d sigma) :
    Coefficients (b.tensorProduct d) (rho.tprod sigma) := by
  rintro ⟨i,j⟩ ⟨k,l⟩
  simp only [Module.Basis.tensorProduct_apply,Representation.tprod_apply,TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply,smul_eq_mul]
  exact (hs j l).mul (hr i k)

variable [IsTopologicalGroup G]
theorem dual [DecidableEq I] (b : Module.Basis I ℂ V) (rho : Representation ℂ G V)
    (hr : Coefficients b rho) : Coefficients b.dualBasis rho.dual := by
  classical
  intro i j
  simp only [Module.Basis.dualBasis_repr,Representation.dual_apply]
  change Continuous (fun g => b.dualBasis i (rho g⁻¹ (b j)))
  simpa only [Module.Basis.dualBasis_apply,Function.comp_def] using (hr j i).comp continuous_inv

variable {K : Type*} [Group K] [TopologicalSpace K]
omit [Fintype I] [IsTopologicalGroup G] in
theorem comp (b : Module.Basis I ℂ V) (rho : Representation ℂ G V)
    (hr : Coefficients b rho) (j : K →* G) (hj : Continuous j) : Coefficients b (rho.comp j) :=
  fun i k => (hr i k).comp hj

variable {S : Type*} [Fintype S] [DecidableEq S]
  {F : S → Type*} [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {B : S → Type*} [∀ s, Fintype (B s)]
  (r : ∀ s, Representation ℂ G (F s)) (b : ∀ s, Module.Basis (B s) ℂ (F s))
  {n : ℕ} (p : Fin n → S)
  {D : Type*} [Fintype D] (d : Module.Basis D ℂ (PatternExteriorSource.Source r p))

omit [IsTopologicalGroup G] in
/-- Continuity descends through the statistical image using its actual pure
source span, not a putative basis of ordered tensor slots. -/
theorem source_copy_continuous (h : ∀ s, Coefficients (b s) (r s)) :
    ContinuousRepresentationScope.IsJointlyContinuous
      (basisCopyRepresentation d (PatternExteriorSource.representation r p)) := by
  apply jointlyContinuous_of_orbit
  intro x
  have hc (y : ⨂[ℂ] i : Fin n, F (p i)) : Continuous (fun g => (Copy.valLinearEquiv d).symm
      (PatternExteriorSource.representation r p g (PatternExteriorSource.onto r p y))) := by
    have hm : y ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ)) := by
      rw [PiTensorProduct.span_tprod_eq_top]; trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v,rfl⟩ := hy
      let q := (Copy.valLinearEquiv d).symm.toLinearMap.compMultilinearMap
        ((PatternExteriorSource.pure r p).compLinearMap (fun i => (Copy.valLinearEquiv (b (p i))).toLinearMap))
      have hq : Continuous q := q.continuous_of_finiteDimensional
      have hv : Continuous (fun g => fun i =>
          basisCopyRepresentation (b (p i)) (r (p i)) g (⟨v i⟩ : Copy (b (p i)))) :=
        continuous_pi (fun i => (copy_continuous (b (p i)) (r (p i)) (h (p i))).orbit _)
      exact (hq.comp hv).congr (fun g => by
        apply (Copy.valLinearEquiv d).injective
        change PatternExteriorSource.pure r p (fun i => r (p i) g (v i)) = _
        exact PatternExteriorSource.pure_action r p g v)
    | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : G => (0 : Copy d)))
    | add y z _ _ hy hz =>
      exact (hy.add hz).congr (fun g => by simp only [map_add,Pi.add_apply])
    | smul c y _ hy =>
      exact (hy.const_smul c).congr (fun g => by simp only [map_smul,Pi.smul_apply])
  obtain ⟨y,hy⟩ := PatternExteriorSource.onto_surjective r p x.val
  exact (hc y).congr (fun g => by
    apply (Copy.valLinearEquiv d).injective
    change PatternExteriorSource.representation r p g (PatternExteriorSource.onto r p y) =
      PatternExteriorSource.representation r p g x.val
    rw [hy])

end
end Math.BasisActionContinuity
