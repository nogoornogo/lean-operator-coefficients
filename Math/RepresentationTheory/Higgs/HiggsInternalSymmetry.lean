import Math.RepresentationTheory.Lagrangian.HiggsLagrangianInput
import Math.RepresentationTheory.Jets.PairedJetContractions

/-! Full nonlinear Higgs equation stability under any paired internal action.
The actual quotient relations are used, not a homogeneous equation truncation. -/
namespace Math.HiggsInternalSymmetry
set_option autoImplicit false
noncomputable section
open Representation DerivativeLiteratureHiggs PairedComponentFields
variable {H : Type*} [Group H] (r : Representation ℂ H (Fin 2 → ℂ))

abbrev act := PairedJetContractions.action (I := Fin 4) r
abbrev transport := PairedJetContractions.transport (I := Fin 4) r
abbrev fields : JetLinear.Field Label →ₗ[ℂ] A :=
  JetLinear.linearForm.comp (JetLinear.atOrder 0)
def boxMap : A →ₗ[ℂ] A :=
  (D 0).toLinearMap.comp (D 0).toLinearMap-
  (D 1).toLinearMap.comp (D 1).toLinearMap-
  (D 2).toLinearMap.comp (D 2).toLinearMap-
  (D 3).toLinearMap.comp (D 3).toLinearMap
def seedMap (a b : ℂ) : JetLinear.Field Label →ₗ[ℂ] A :=
  boxMap.comp fields+a • fields+b • ((LinearMap.mulLeft ℂ rho).comp fields)

theorem seedMap_apply (a b : ℂ) (v : JetLinear.Field Label) :
    seedMap a b v = box (fields v)+a • fields v+b • (rho*fields v) := rfl

theorem fields_single (j : Label) : fields (Finsupp.single j 1) = h j.1 j.2 := by
  simp [fields,JetLinear.linearForm,h]

theorem seedMap_single (a b : ℂ) (j : Label) :
    seedMap a b (Finsupp.single j 1) = seed a b j := by
  rw [seedMap_apply,fields_single]
  simp [seed,Algebra.smul_def,MvPolynomial.algebraMap_eq,mul_assoc]

theorem radius_invariant (g : H) : transport r g rho = rho := by
  have he : rho = PairedJetContractions.canonical (ι := Fin 2)
      (I := Fin 4) 0 0 := by
    rw [PairedJetContractions.canonical_formula]
    simp [rho,h,Fin.sum_univ_two,mul_comm]
  rw [he]
  exact PairedJetContractions.canonical_invariant r g 0 0

theorem derivative_commute (g : H) (i : Fin 4) (p : A) :
    transport r g (D i p) = D i (transport r g p) := by
  have hc (v : JetLinear.Jet Label (Fin 4)) :
      JetLinear.action (PairedComponentFields.action r) g (JetLinear.shift i v) =
        ∑ k : Fin 4, ((Pi.single i (1:ℂ)) : Fin 4 → ℂ) k •
          JetLinear.shift k (JetLinear.action (PairedComponentFields.action r) g v) := by
    change JetLinear.map _ (JetLinear.shift i v) = _
    rw [JetLinear.map_shift]
    simp [Pi.single_apply]
    rfl
  have hp := JetFunctor.polynomial_covariant
    (JetLinear.action (I := Fin 4) (PairedComponentFields.action r)) g i _ hc p
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at hp
  change JetFunctor.polynomialMap (JetLinear.map (PairedComponentFields.action r g))
      (ScalarJetAlgebra.totalDerivative i p) =
    ScalarJetAlgebra.totalDerivative i
      (JetFunctor.polynomialMap (JetLinear.map (PairedComponentFields.action r g)) p) at hp
  exact hp

theorem fields_covariant (g : H) (v : JetLinear.Field Label) :
    transport r g (fields v) = fields (PairedComponentFields.action r g v) := by
  change JetFunctor.polynomialMap _ (JetLinear.linearForm _) = _
  rw [JetFunctor.polynomialMap_linearForm,JetLinear.map_atOrder]
  rfl

theorem seedMap_covariant (a b : ℂ) (g : H) (v : JetLinear.Field Label) :
    transport r g (seedMap a b v) = seedMap a b (PairedComponentFields.action r g v) := by
  rw [seedMap_apply,seedMap_apply]
  simp only [box,map_add,map_sub,map_smul,map_mul,derivative_commute,
    fields_covariant,radius_invariant]

theorem seedMap_mem (a b : ℂ) (v : JetLinear.Field Label) :
    seedMap a b v ∈ DifferentialEquation.ideal D (seeds a b) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using
      (DifferentialEquation.ideal D (seeds a b)).add_mem hv hw
  | single j c =>
    rw [show Finsupp.single j c = c • Finsupp.single j (1:ℂ) by simp,map_smul,
      seedMap_single]
    exact (DifferentialEquation.relations D (seeds a b)).smul_mem c
      (DifferentialEquation.seed_mem D _ ⟨j,rfl⟩)

theorem ideal_stable (a b : ℂ) (g : H) :
    ∀ p ∈ DifferentialEquation.ideal D (seeds a b),
      transport r g p ∈ DifferentialEquation.ideal D (seeds a b) := by
  apply DifferentialEquation.map_stable
  · rintro p ⟨j,rfl⟩
    rw [← seedMap_single,seedMap_covariant]
    exact seedMap_mem a b _
  · intro i p hp
    rw [derivative_commute]
    exact DifferentialEquation.stable D _ i hp

end
end Math.HiggsInternalSymmetry
