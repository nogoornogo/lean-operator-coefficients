import Math.Algebra.Jets.JetDirections

/-! Component and direction actions on the same unbounded jet module. -/
namespace Math.JetDirections
set_option autoImplicit false
noncomputable section
open MvPolynomial JetLinear ScalarJetAlgebra

variable {S T I : Type*}

def attach (p : Symbols I) : JetLinear.Field S →ₗ[ℂ] Jet S I :=
  Finsupp.linearCombination ℂ (fun s => ofSymbols s p)

@[simp] theorem attach_single (p : Symbols I) (s : S) (c : ℂ) :
    attach p (Finsupp.single s c) = c • ofSymbols s p := by simp [attach]

theorem attach_monomial (α : I →₀ ℕ) (c : ℂ) (v : JetLinear.Field S) :
    attach (monomial α c) v = c • atOrder α v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]
  | single s r => simp only [attach_single, ofSymbols_monomial, atOrder_single]
                  simp [Finsupp.smul_single, mul_comm]

theorem internal_ofSymbols (f : JetLinear.Field S →ₗ[ℂ] JetLinear.Field T) (s : S) (p : Symbols I) :
    JetLinear.map f (ofSymbols s p) = attach p (f (Finsupp.single s 1)) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c => simp [attach_monomial]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    simp [attach, Finsupp.linearCombination_apply, Finsupp.sum_add, smul_add]

theorem jetMap_atOrder (g : Direction I →ₗ[ℂ] Direction I) (α : I →₀ ℕ) (v : JetLinear.Field S) :
    jetMap g (atOrder α v) = attach (symbolMap g (monomial α 1)) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c => simp [jetMap]

theorem internal_commute (f : JetLinear.Field S →ₗ[ℂ] JetLinear.Field T)
    (g : Direction I →ₗ[ℂ] Direction I) (x : Jet S I) :
    jetMap g (JetLinear.map f x) = JetLinear.map f (jetMap g x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single j c =>
    obtain ⟨s, α⟩ := j
    simp only [JetLinear.map_single, map_smul]
    rw [jetMap_atOrder]
    simp only [jetMap, lift_single, map_smul,
      AlgHom.toLinearMap_apply, internal_ofSymbols]

def combined {H : Type*} [Monoid H] (ρ : Representation ℂ H (JetLinear.Field S))
    (σ : Representation ℂ H (Direction I)) : Representation ℂ H (Jet S I) where
  toFun h := (JetLinear.map (ρ h)).comp (jetMap (σ h))
  map_one' := by
    rw [ρ.map_one, σ.map_one]
    change (JetLinear.map LinearMap.id).comp (jetMap LinearMap.id) = LinearMap.id
    rw [JetLinear.map_id, jetMap_id]; rfl
  map_mul' h k := by
    rw [ρ.map_mul, σ.map_mul]
    change (JetLinear.map ((ρ h).comp (ρ k))).comp (jetMap ((σ h).comp (σ k))) =
      ((JetLinear.map (ρ h)).comp (jetMap (σ h))).comp
        ((JetLinear.map (ρ k)).comp (jetMap (σ k)))
    rw [JetLinear.map_comp, jetMap_comp]
    apply LinearMap.ext
    intro x
    exact congrArg (JetLinear.map (ρ h)) (internal_commute (ρ k) (σ h) (jetMap (σ k) x)).symm

theorem combined_covariant [Fintype I] {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (h : H) (i : I) (x : Jet S I) :
    combined ρ σ h (JetLinear.shift i x) =
      ∑ j, (σ h (Finsupp.single i 1)) j • JetLinear.shift j (combined ρ σ h x) := by
  change JetLinear.map (ρ h) (jetMap (σ h) (JetLinear.shift i x)) = _
  rw [jetMap_covariant, map_sum]
  simp only [map_smul, JetLinear.map_shift]
  rfl

theorem atOrder_mem (α : I →₀ ℕ) (v : JetLinear.Field S) : atOrder α v ∈ jetOrder S I (order α) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | single s c => rw [atOrder_single]; exact Finsupp.single_mem_supported ℂ c rfl

theorem internal_order (f : JetLinear.Field S →ₗ[ℂ] JetLinear.Field T) {d : ℕ} {v : Jet S I}
    (hv : v ∈ jetOrder S I d) : JetLinear.map f v ∈ jetOrder T I d := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨s, α⟩ := j
  change JetLinear.map f (Finsupp.single (s, α) (v (s, α))) ∈ _
  rw [JetLinear.map_single]
  apply Submodule.smul_mem
  have he : order α = d := hv hj
  exact he ▸ atOrder_mem α (f (Finsupp.single s 1))

theorem combined_order {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (h : H) (d : ℕ) : jetOrder S I d ≤ (jetOrder S I d).comap (combined ρ σ h) :=
  fun _ hp => internal_order (ρ h) (jetMap_order (σ h) hp)

theorem jetMap_zero (f : Direction I →ₗ[ℂ] Direction I) (v : JetLinear.Field S) :
    jetMap f (atOrder 0 v) = atOrder 0 v := by
  rw [jetMap_atOrder]
  have hm : monomial (0 : I →₀ ℕ) (1 : ℂ) = (1 : Symbols I) := by simp
  rw [hm, map_one]
  simpa only [hm, one_smul] using attach_monomial (I := I) 0 1 v

theorem combined_zero {H : Type*} [Monoid H]
    (ρ : Representation ℂ H (JetLinear.Field S)) (σ : Representation ℂ H (Direction I))
    (h : H) (v : JetLinear.Field S) : combined ρ σ h (atOrder 0 v) = atOrder 0 (ρ h v) := by
  change JetLinear.map (ρ h) (jetMap (σ h) (atOrder 0 v)) = _
  rw [jetMap_zero, JetLinear.map_atOrder]

theorem combined_trivial {H : Type*} [Monoid H] (σ : Representation ℂ H (Direction I)) (h : H) :
    combined (Representation.trivial ℂ H (JetLinear.Field S)) σ h = jetMap (σ h) := by
  change (JetLinear.map LinearMap.id).comp (jetMap (σ h)) = _
  rw [JetLinear.map_id]
  rfl

end
end Math.JetDirections
