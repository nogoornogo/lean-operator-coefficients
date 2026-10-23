import Math.RepresentationTheory.Content.MixedPatternAssembly
import Math.RepresentationTheory.Content.MixedSpeciesPartition

/-! Finite field-content orbits at arbitrary mixed degrees. No orbit representatives
or lists of contractions are supplied as hypotheses. -/
namespace Math.MixedContentOrbits
set_option autoImplicit false
noncomputable section
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {n m : ℕ}

private theorem permute_orbit {S : Type*} {d : ℕ} (x y : Fin d → S)
    (p : Equiv.Perm (Fin d)) :
    (∃ q : Equiv.Perm (Fin d), (x ∘ p) ∘ q = y) ↔
      ∃ q : Equiv.Perm (Fin d), x ∘ q = y := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨p * q, hq⟩
  · rintro ⟨q, hq⟩
    refine ⟨p⁻¹ * q, ?_⟩
    funext i
    simpa only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
      Equiv.apply_symm_apply] using congrFun hq i

def setoid : Setoid ((Fin n → P) × (Fin m → Q)) where
  r x y := MixedPatternAssembly.Orbit y.1 y.2 x.1 x.2
  iseqv := ⟨fun x => ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩, by
      intro x y h
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
      constructor
      · refine ⟨p⁻¹, ?_⟩
        funext i
        have he := congrFun hp (p⁻¹ i)
        simpa only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using he.symm
      · refine ⟨q⁻¹, ?_⟩
        funext i
        have he := congrFun hq (q⁻¹ i)
        simpa only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using he.symm,
    by
      intro x y z hxy hyz
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hxy
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hyz
      constructor
      · refine ⟨p * a, ?_⟩
        exact (congrArg (fun f => f ∘ a) hp).trans ha
      · refine ⟨q * b, ?_⟩
        exact (congrArg (fun f => f ∘ b) hq).trans hb⟩

abbrev Content := Quotient (setoid (P := P) (Q := Q) (n := n) (m := m))

instance : Fintype (Content (P := P) (Q := Q) (n := n) (m := m)) := by
  classical
  exact Quotient.fintype _

def support (c : Content (P := P) (Q := Q) (n := n) (m := m))
    (labels : Fin n → P) (scalars : Fin m → Q) : Prop :=
  MixedPatternAssembly.Orbit c.out.1 c.out.2 labels scalars

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem support_iff (c : Content (P := P) (Q := Q) (n := n) (m := m))
    (labels : Fin n → P) (scalars : Fin m → Q) :
    support c labels scalars ↔ Quotient.mk _ (labels, scalars) = c := by
  change (setoid (P := P) (Q := Q) (n := n) (m := m)).r (labels, scalars) c.out ↔ _
  rw [← Quotient.eq, Quotient.out_eq]

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem stable (c : Content (P := P) (Q := Q) (n := n) (m := m))
    (labels : Fin n → P) (scalars : Fin m → Q)
    (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)) :
    support c (labels ∘ p) (scalars ∘ q) ↔ support c labels scalars :=
  and_congr (permute_orbit labels c.out.1 p) (permute_orbit scalars c.out.2 q)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem disjoint (c d : Content (P := P) (Q := Q) (n := n) (m := m))
    (hcd : c ≠ d) (labels : Fin n → P) (scalars : Fin m → Q)
    (hc : support c labels scalars) : ¬ support d labels scalars := by
  intro hd
  exact hcd ((support_iff c labels scalars).mp hc |>.symm.trans
    ((support_iff d labels scalars).mp hd))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem covers (labels : Fin n → P) (scalars : Fin m → Q) :
    ∃ c : Content (P := P) (Q := Q) (n := n) (m := m), support c labels scalars :=
  ⟨Quotient.mk _ (labels, scalars), (support_iff _ _ _).mpr rfl⟩

section Coefficients
open Representation FiniteSpeciesExterior
variable {G : Type*} [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))

private theorem partition_top : MixedSpeciesPartition.partitionSpace r t
    (support (P := P) (Q := Q) (n := n) (m := m)) = ⊤ := by
  apply top_unique
  intro f hf labels scalars hn v w
  exact False.elim (hn (covers labels scalars))

/-- All mixed coefficients split into exactly one factor for each species-content orbit. -/
def equiv : MixedWeightSupport.Coefficient (representation r) (representation t) (n := n) (m := m)
    ≃ₗ[ℂ] (∀ c : Content (P := P) (Q := Q) (n := n) (m := m),
      MixedPatternAssembly.orderedSpace r t c.out.1 c.out.2) := by
  classical
  exact (Submodule.topEquiv.symm.trans
    ((LinearEquiv.ofEq _ _ (partition_top r t).symm).trans
      (MixedSpeciesPartition.equiv r t support stable disjoint))).trans
    (LinearEquiv.piCongrRight fun c => MixedPatternAssembly.equiv r t c.out.1 c.out.2)

section Selection
variable (allow : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ labels scalars, Decidable (allow labels scalars)]
  (stableAllow : ∀ labels scalars (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    allow (labels ∘ p) (scalars ∘ q) ↔ allow labels scalars)

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ labels scalars, Decidable (allow labels scalars)] in
include stableAllow in
theorem support_allow (c : Content (P := P) (Q := Q) (n := n) (m := m))
    (labels : Fin n → P) (scalars : Fin m → Q) (hc : support c labels scalars) :
    allow c.out.1 c.out.2 ↔ allow labels scalars := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc
  simpa only [hp, hq] using stableAllow labels scalars p q

abbrev Selected := {c : Content (P := P) (Q := Q) (n := n) (m := m) | allow c.out.1 c.out.2}

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ labels scalars, Decidable (allow labels scalars)] in
include stableAllow in
theorem selected_covers (labels : Fin n → P) (scalars : Fin m → Q) :
    (∃ c : Selected allow, support c.val labels scalars) ↔ allow labels scalars := by
  constructor
  · rintro ⟨c, hc⟩
    exact (support_allow allow stableAllow c.val labels scalars hc).mp c.property
  · intro ha
    obtain ⟨c, hc⟩ := covers labels scalars
    exact ⟨⟨c, (support_allow allow stableAllow c labels scalars hc).mpr ha⟩, hc⟩

omit [∀ labels scalars, Decidable (allow labels scalars)] in
include stableAllow in
private theorem selected_partition_eq : MixedSpeciesProjection.supportSpace allow r t =
    MixedSpeciesPartition.partitionSpace r t (fun c : Selected allow => support c.val) := by
  apply le_antisymm
  · intro f hf labels scalars hn v w
    exact hf labels scalars (fun ha => hn ((selected_covers allow stableAllow labels scalars).mpr ha)) v w
  · intro f hf labels scalars hn v w
    exact hf labels scalars (fun hc => hn ((selected_covers allow stableAllow labels scalars).mp hc)) v w

/-- Charge and engineering support is selected before the content-wise typed restriction. -/
def selectedEquiv : MixedSpeciesProjection.supportSpace allow r t ≃ₗ[ℂ]
    (∀ c : Selected allow, MixedPatternAssembly.orderedSpace r t c.val.out.1 c.val.out.2) := by
  classical
  exact ((LinearEquiv.ofEq _ _ (selected_partition_eq r t allow stableAllow)).trans
    (MixedSpeciesPartition.equiv r t (fun c : Selected allow => support c.val)
      (fun c => stable c.val) (fun c d hcd => disjoint c.val d.val
        (fun he => hcd (Subtype.ext he))))).trans
    (LinearEquiv.piCongrRight fun c => MixedPatternAssembly.equiv r t c.val.out.1 c.val.out.2)

end Selection

end Coefficients
end
end Math.MixedContentOrbits
