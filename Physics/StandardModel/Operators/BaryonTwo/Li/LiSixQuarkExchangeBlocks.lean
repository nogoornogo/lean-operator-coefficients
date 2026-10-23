import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkProbeDecomposition

/-! Up-slot exchange projectors, derived from the permutation action rather
than a closed matrix involution check. They separate the probe kernel into
smaller symbolic reconstruction problems. -/
namespace Physics.LiSixQuarkExchangeBlocks
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient LiSixQuarkExtension

/-- Exchange of the two up slots, retaining all color/spin coordinates. -/
def exchange : LocalArray →ₗ[ℂ] LocalArray where
  toFun c := transform c 0
  map_add' c d := by
    ext p q
    simp [transform, mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    ext p q
    simp only [transform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

private theorem swap_twice (f : Coefficient) :
    (f.domDomCongr (slotSwap 0)).domDomCongr (slotSwap 0) = f := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply]
  have hv : (fun i => v (slotSwap 0 (slotSwap 0 i))) = v := by
    funext i
    change v (Equiv.swap 0 2 (Equiv.swap 0 2 i)) = v i
    rw [Equiv.swap_apply_self]
  exact congrArg f hv

theorem exchange_involutive (c : LocalArray) : exchange (exchange c) = c := by
  have h : Function.Injective SixQuarkInvariant.reconstruct := by
    intro a b hab
    simpa only [coordinates_reconstruct] using congrArg coordinates hab
  apply h
  change SixQuarkInvariant.reconstruct (transform (transform c 0) 0) = _
  rw [reconstruct_transform, reconstruct_transform, swap_twice]

def evenPart (c : LocalArray) : LocalArray := (1 / 2 : ℂ) • (c + exchange c)
def oddPart (c : LocalArray) : LocalArray := (1 / 2 : ℂ) • (c - exchange c)

theorem reconstruct (c : LocalArray) : evenPart c + oddPart c = c := by
  ext p q
  simp only [evenPart, oddPart, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem even_exchange (c : LocalArray) : exchange (evenPart c) = evenPart c := by
  rw [evenPart, map_smul, map_add, exchange_involutive]
  congr 1
  exact add_comm _ _

theorem odd_exchange (c : LocalArray) : exchange (oddPart c) = -oddPart c := by
  rw [oddPart, map_smul, map_sub, exchange_involutive]
  ext p q
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem probe_exchange (c : LocalArray) : extraProbeLinear (exchange c) = -extraProbeLinear c := by
  change extraProbe (transform c 0) = -extraProbe c
  rw [extraProbe_transform]
  simp [localSign]

theorem even_mem_kernel (c : LocalArray) :
    evenPart c ∈ LinearMap.ker extraProbeLinear := by
  change extraProbeLinear (evenPart c) = 0
  rw [evenPart, map_smul, map_add, probe_exchange, add_neg_cancel, smul_zero]

theorem odd_mem_kernel (c : LocalArray) (hc : c ∈ LinearMap.ker extraProbeLinear) :
    oddPart c ∈ LinearMap.ker extraProbeLinear := by
  change extraProbeLinear (oddPart c) = 0
  rw [oddPart, map_smul, map_sub, probe_exchange]
  change (1 / 2 : ℂ) • (extraProbeLinear c - -extraProbeLinear c) = 0
  rw [show extraProbeLinear c = 0 from hc]
  simp

/-- The two symmetry components are determined by their sum. -/
theorem blocks_unique (a b : LocalArray) (ha : exchange a = a)
    (hb : exchange b = -b) : evenPart (a + b) = a ∧ oddPart (a + b) = b := by
  constructor
  · unfold evenPart
    rw [map_add, ha, hb]
    ext p q
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    ring
  · unfold oddPart
    rw [map_add, ha, hb]
    ext p q
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring

/-- Reconstruction needs only the even and odd kernel blocks, separately. -/
theorem kernel_le_iff_blocks (S : Submodule ℂ LocalArray) :
    LinearMap.ker extraProbeLinear ≤ S ↔
      (∀ c, exchange c = c → c ∈ S) ∧
      (∀ c, exchange c = -c → c ∈ LinearMap.ker extraProbeLinear → c ∈ S) := by
  constructor
  · intro h
    refine ⟨?_, fun c _ hc => h hc⟩
    intro c hc
    apply h
    have hp := probe_exchange c
    rw [hc] at hp
    change extraProbeLinear c = 0
    linear_combination (1 / 2 : ℂ) * hp
  · rintro ⟨he, ho⟩ c hc
    rw [← reconstruct c]
    exact S.add_mem (he _ (even_exchange c)) (ho _ (odd_exchange c) (odd_mem_kernel c hc))

end
end Physics.LiSixQuarkExchangeBlocks
