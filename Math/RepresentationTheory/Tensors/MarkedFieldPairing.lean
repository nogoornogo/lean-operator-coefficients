import Math.RepresentationTheory.Color.Diagrams.ColoredWavePairing

/-! A marked charge insertion in the symmetric quartic field/dual pairing.
It commutes with every paired internal action. -/
namespace Math.MarkedFieldPairing
set_option autoImplicit false
noncomputable section
open PairedComponentFields ColoredWavePairing

def charge : Fields →ₗ[ℂ] Fields := fieldEquiv.symm.toLinearMap.comp
  (((LinearMap.id : V (Fin 2) →ₗ[ℂ] V (Fin 2)).prodMap
    (-LinearMap.id : Module.Dual ℂ (V (Fin 2)) →ₗ[ℂ] Module.Dual ℂ (V (Fin 2)))).comp
      fieldEquiv.toLinearMap)

theorem charge_action {H : Type*} [Group H] (rho : Representation ℂ H (V (Fin 2)))
    (g : H) (v : Fields) : charge (action rho g v) = action rho g (charge v) := by
  apply fieldEquiv.injective
  simp [charge,fieldEquiv_action]

def sign (j : Label) : ℂ := if j.1 then -1 else 1
theorem charge_single (j : Label) : charge (Finsupp.single j 1) = sign j • Finsupp.single j 1 := by
  apply fieldEquiv.injective
  rcases j with ⟨c,a⟩
  cases c <;> simp [charge,sign,fieldEquiv_false,fieldEquiv_true]

def symmetric : MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ := ∑ p : Fin 24, tensor p
def marked : MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ :=
  symmetric.compLinearMap (fun t => if t = 0 then charge else LinearMap.id)

theorem symmetric_invariant {H : Type*} [Group H]
    (rho : Representation ℂ H (V (Fin 2))) (g : H) (v : Fin 4 → Fields) :
    symmetric (fun t => action rho g (v t)) = symmetric v := by
  simp [symmetric,tensor_invariant]

theorem marked_invariant {H : Type*} [Group H]
    (rho : Representation ℂ H (V (Fin 2))) (g : H) (v : Fin 4 → Fields) :
    marked (fun t => action rho g (v t)) = marked v := by
  simp only [marked,MultilinearMap.compLinearMap_apply]
  have he : (fun t : Fin 4 => (if t = 0 then charge else LinearMap.id) (action rho g (v t))) =
      (fun t => action rho g ((if t = 0 then charge else LinearMap.id) (v t))) := by
    funext t
    by_cases ht : t = 0 <;> simp [ht,charge_action]
  rw [he,symmetric_invariant]

theorem marked_basis (b : Fin 4 → Label) :
    marked (fun t => Finsupp.single (b t) 1) =
      sign (b 0) * ∑ p : Fin 24, tensor p (fun t => Finsupp.single (b t) 1) := by
  simp only [marked,MultilinearMap.compLinearMap_apply]
  have he : (fun t : Fin 4 => (if t = 0 then charge else LinearMap.id) (Finsupp.single (b t) 1)) =
      (fun t => (if t = 0 then sign (b 0) else 1) • Finsupp.single (b t) 1) := by
    funext t
    by_cases ht : t = 0 <;> simp [ht,charge_single]
  rw [he,MultilinearMap.map_smul_univ]
  simp [symmetric]

end
end Math.MarkedFieldPairing
