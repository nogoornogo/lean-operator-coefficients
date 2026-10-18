import Math.Audit.ImportOrigin
import GUT.SU5.Embeddings.StandardModelQuotient


/-! Persistent audit of the actual SU(5) map, its central kernel, and its
quotient topology. Neither the ambient SU(6) group nor its source bridges
are inputs to this development. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(5) embedding audit imports SU(6): {mod}"

namespace GUT.SU5.AuditStandardModelEmbedding

noncomputable section

open StandardModelEmbedding StandardSMGaugeTensor

theorem color_first_convention (g : GaugeGroup) :
    (hom g : Matrix (Fin 5) (Fin 5) ℂ) 0 0 =
      phase (-2) g * (g.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 ∧
    (hom g : Matrix (Fin 5) (Fin 5) ℂ) 3 3 =
      phase 3 g * (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
  ⟨hom_color_entry g 0 0, hom_weak_entry g 0 0⟩

theorem sign_kernel_coordinates :
    (signKernelElement.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 ∧
    (signKernelElement.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = -1 ∧
    signKernelElement.2.2 = -1 := by
  norm_num [signKernelElement, kernelElement, scalarSpecialUnitary]

theorem cover_has_collision :
    signKernelElement ≠ 1 ∧ hom signKernelElement = hom 1 :=
  ⟨signKernelElement_ne_one, hom_signKernelElement.trans (map_one hom).symm⟩

/-- A circle sign by itself is not killed: its compensating weak center is essential. -/
theorem circle_sign_not_in_kernel : (1, 1, (-1 : Circle)) ∉ hom.ker := by
  intro h
  have hw := ((hom_eq_one_iff (1, 1, (-1 : Circle))).mp h).2.2
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hw
  norm_num at he

theorem sign_killed_in_quotient :
    (QuotientGroup.mk signKernelElement : SMQuotient) = 1 := by
  apply quotientHom_injective
  simp

theorem circle_sign_survives_quotient :
    (QuotientGroup.mk (1, 1, (-1 : Circle)) : SMQuotient) ≠ 1 := by
  intro h
  apply circle_sign_not_in_kernel
  change hom (1, 1, (-1 : Circle)) = 1
  have he := congrArg quotientHom h
  simpa using he

example : IsCyclic hom.ker := inferInstance
example : Nat.card hom.ker = 6 := kernel_card
example : CompactSpace SMQuotient := inferInstance
example : IsTopologicalGroup SMQuotient := inferInstance
example : T2Space SMQuotient := inferInstance
example : Function.Injective quotientContinuousHom := quotientHom_injective
example : Continuous quotientImageEquiv.symm := quotientImageEquiv.symm.continuous

#print axioms continuousHom
#print axioms hom_eq_one_iff
#print axioms mem_ker_iff
#print axioms kernelRootsEquiv
#print axioms kernelCyclicEquiv
#print axioms kernel_card
#print axioms kernel_isCyclic
#print axioms kernel_le_center
#print axioms hom_not_injective
#print axioms quotientHom_injective
#print axioms quotientHom_isClosedEmbedding
#print axioms quotientImageEquiv
#print axioms quotientImageEquiv_mk
#print axioms image_isClosed
#print axioms color_first_convention
#print axioms sign_kernel_coordinates
#print axioms cover_has_collision
#print axioms circle_sign_not_in_kernel
#print axioms sign_killed_in_quotient
#print axioms circle_sign_survives_quotient

end

end GUT.SU5.AuditStandardModelEmbedding
