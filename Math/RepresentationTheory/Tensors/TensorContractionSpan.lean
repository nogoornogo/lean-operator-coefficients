import Math.RepresentationTheory.Tensors.TensorVolumeSplit
import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-! A determinant split and a proved tensor commutant supply actual mixed
contraction spanning. The commutant is an explicit construction input to this
helper; the two color applications discharge it by Schur-Weyl. -/
namespace Math.TensorContractionSpan
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {n : ℕ}
  (rho : Representation ℂ G V) (b : Module.Basis (Fin n) ℂ V)
  (hd : ∀ g, LinearMap.det (rho g) = 1)

@[reducible] local instance (m : ℕ) : AddCommGroup (⨂[ℂ]^m V) := inferInstance
@[reducible] local instance (m : ℕ) : AddCommGroup (⨂[ℂ]^m (Module.Dual ℂ V)) := inferInstance
@[reducible] local instance (p q : ℕ) :
    AddCommGroup ((⨂[ℂ]^p V) ⊗[ℂ] (⨂[ℂ]^q (Module.Dual ℂ V))) := inferInstance

abbrev perm (m : ℕ) := PiTensorProduct.reindexRepresentation ℂ V (Fin m)
abbrev permAlgebra (m : ℕ) := (perm (V := V) m).asAlgebraHom

def Commutant : Prop := ∀ m (f : Module.End ℂ (⨂[ℂ]^m V)),
  (∀ g, Commute f ((rho.tensorPower m) g)) →
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin m)), permAlgebra m a = f

def permutation (m : ℕ) (sigma : Equiv.Perm (Fin m)) :
    IntertwiningMap (rho.tensorPower m) (rho.tensorPower m) where
  toLinearMap := perm m sigma
  isIntertwining' g := (PiTensorProduct.commute_reindexRepresentation_map
    ℂ V (Fin m) sigma (rho g)).eq

def contraction (q k : ℕ) (sigma : Equiv.Perm (Fin (q+n*k))) :
    IntertwiningMap ((rho.tensorPower (q+n*k)).tprod (rho.dual.tensorPower q)) (trivial ℂ G ℂ) :=
  (TensorPowerDualEquivalence.curry rho (q+n*k) q).symm
    ((TensorVolumeSplit.raiseDegree rho b hd q k).project.comp (permutation rho (q+n*k) sigma))

theorem contraction_apply (q k : ℕ) (sigma : Equiv.Perm (Fin (q+n*k)))
    (x : ⨂[ℂ]^(q+n*k) V) (y : ⨂[ℂ]^q (Module.Dual ℂ V)) :
    contraction rho b hd q k sigma (x ⊗ₜ[ℂ] y) =
      TensorPowerDualEquivalence.equivalence rho q y
        ((TensorVolumeSplit.raiseDegree rho b hd q k).project (perm (q+n*k) sigma x)) := by
  have he := TensorPowerDualEquivalence.curry_apply rho (q+n*k) q
    (contraction rho b hd q k sigma) x y
  rw [show TensorPowerDualEquivalence.curry rho (q+n*k) q
      (contraction rho b hd q k sigma) =
        (TensorVolumeSplit.raiseDegree rho b hd q k).project.comp (permutation rho (q+n*k) sigma) from
    (TensorPowerDualEquivalence.curry rho (q+n*k) q).apply_symm_apply _] at he
  exact he.symm

omit [FiniteDimensional ℂ V] in
theorem hom_image (hc : Commutant rho) (q k : ℕ)
    (f : IntertwiningMap (rho.tensorPower (q+n*k)) (rho.tensorPower q)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin (q+n*k))),
      f.toLinearMap = (TensorVolumeSplit.raiseDegree rho b hd q k).project.toLinearMap ∘ₗ
        permAlgebra (q+n*k) a := by
  let S := TensorVolumeSplit.raiseDegree rho b hd q k
  let e := S.embed.comp f
  obtain ⟨a,ha⟩ := hc (q+n*k) e.toLinearMap (fun g => e.isIntertwining' g)
  refine ⟨a,?_⟩
  rw [ha]
  apply LinearMap.ext
  intro x
  exact (S.left_inv (f x)).symm

theorem spanning (hc : Commutant rho) (q k : ℕ)
    (f : IntertwiningMap ((rho.tensorPower (q+n*k)).tprod (rho.dual.tensorPower q)) (trivial ℂ G ℂ)) :
    ∃ c : Equiv.Perm (Fin (q+n*k)) → ℂ,
      f = ∑ sigma, c sigma • contraction rho b hd q k sigma := by
  let F := TensorPowerDualEquivalence.curry rho (q+n*k) q f
  obtain ⟨a,ha⟩ := hom_image rho b hd hc q k F
  refine ⟨a.coeff,?_⟩
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  have he := TensorPowerDualEquivalence.curry_apply rho (q+n*k) q f x y
  change TensorPowerDualEquivalence.equivalence rho q y (F.toLinearMap x) = f (x ⊗ₜ[ℂ] y) at he
  rw [ha] at he
  change f (x ⊗ₜ[ℂ] y) =
    (∑ sigma, a.coeff sigma • contraction rho b hd q k sigma) (x ⊗ₜ[ℂ] y)
  rw [← he]
  have halg : permAlgebra (V := V) (q+n*k) a =
      ∑ sigma, a.coeff sigma • perm (q+n*k) sigma := by
    simp [permAlgebra,Representation.asAlgebraHom_def,MonoidAlgebra.lift_apply,Finsupp.sum_fintype]
  rw [halg]
  simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.sum_apply,IntertwiningMap.smul_apply,contraction_apply]
  rfl

end
end Math.TensorContractionSpan
