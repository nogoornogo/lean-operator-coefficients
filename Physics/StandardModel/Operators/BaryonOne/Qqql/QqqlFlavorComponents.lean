import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExteriorCompleteness
import Math.RepresentationTheory.Unitary.FourDoubletProductComponents
import Math.RepresentationTheory.Constructions.TripleMixedCoordinates
import Math.RepresentationTheory.Content.TripleFlavorCoordinates

open Math

/-! Explicit symmetric, alternating and mixed residual flavor coordinates for qqql. -/
namespace Physics.QqqlFlavorComponents
set_option autoImplicit false
noncomputable section
open Representation QqqlExchange FourDoubletProductComponents
open scoped TensorProduct
variable {H Q L : Type*} [Group H] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ H Q) (l : Representation ℂ H L)

abbrev Family := Fin 4 → Residual q l

def values (f : Family q l) (x y z : Q) (h : L) : Components :=
  fun i => f i ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))

def Condition (f : Family q l) : Prop := ∀ x y z h,
  action01 (values q l f y x z h) = values q l f x y z h ∧
  action12 (values q l f x z y h) = values q l f x y z h

theorem values_extract (k : QqqlExchange.Family q l) (x y z : Q) (h : L) :
    values q l (extractModule k) x y z h =
      extract (QqqlExchange.values q l k x y z h) := by
  funext i
  fin_cases i <;> simp [values, extractModule, extract, QqqlExchange.values,
    smul_eq_mul] <;> ring

theorem condition_iff (k : QqqlExchange.Family q l) :
    QqqlExchange.Condition q l k ↔ Condition q l (extractModule k) := by
  constructor
  · intro hk x y z h
    simp only [values_extract]
    obtain ⟨h01, h12⟩ := hk x y z h
    constructor
    · rw [← extract_exchange01, h01]
    · rw [← extract_exchange12, h12]
  · intro hk x y z h
    obtain ⟨h01, h12⟩ := hk x y z h
    simp only [values_extract, ← extract_exchange01, ← extract_exchange12] at h01 h12
    exact ⟨equiv.injective h01, equiv.injective h12⟩

theorem values_assemble (f : Family q l) (x y z : Q) (h : L) :
    QqqlExchange.values q l (assembleModule f) x y z h =
      assemble (values q l f x y z h) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [QqqlExchange.values, values,
    assembleModule, assemble, smul_eq_mul]

def residualSpace : Submodule ℂ (Family q l) :=
  (QqqlExchange.residualSpace q l).map moduleEquiv.toLinearMap

theorem mem_residualSpace_iff (f : Family q l) :
    f ∈ residualSpace q l ↔ Condition q l f := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (condition_iff q l k).mp hk
  · intro hf
    refine ⟨moduleEquiv.symm f, ?_, moduleEquiv.apply_symm_apply f⟩
    apply (condition_iff q l _).mpr
    change Condition q l (moduleEquiv (moduleEquiv.symm f))
    simpa only [LinearEquiv.apply_symm_apply] using hf

def residualEquiv : QqqlExchange.residualSpace q l ≃ₗ[ℂ] residualSpace q l :=
  (ConstrainedCompleteness.Presentation.mk moduleEquiv (by
    intro k
    rw [mem_residualSpace_iff]
    exact condition_iff q l k)).equiv

def exteriorEquiv : QqqlExteriorCompleteness.Sector q l ≃ₗ[ℂ] residualSpace q l :=
  (QqqlExteriorCompleteness.exteriorEquiv q l).trans (residualEquiv q l)

theorem inverse_left (f : QqqlExteriorCompleteness.Sector q l) :
    (exteriorEquiv q l).symm (exteriorEquiv q l f) = f :=
  (exteriorEquiv q l).symm_apply_apply f

theorem inverse_right (f : residualSpace q l) :
    exteriorEquiv q l ((exteriorEquiv q l).symm f) = f :=
  (exteriorEquiv q l).apply_symm_apply f

/-- The mixed part is encoded by its final coordinate: symmetric in its last
two Q inputs and with vanishing cyclic sum. -/
theorem component_relations (f : residualSpace q l) (x y z : Q) (h : L) :
    values q l f.val y x z h 0 = values q l f.val x y z h 0 ∧
    values q l f.val x z y h 0 = values q l f.val x y z h 0 ∧
    values q l f.val y x z h 1 = -values q l f.val x y z h 1 ∧
    values q l f.val x z y h 1 = -values q l f.val x y z h 1 ∧
    values q l f.val x y z h 2 = values q l f.val y x z h 3 ∧
    values q l f.val x z y h 3 = values q l f.val x y z h 3 ∧
    values q l f.val x y z h 3 + values q l f.val y x z h 3 +
      values q l f.val z x y h 3 = 0 := by
  have hf := (mem_residualSpace_iff q l f.val).mp f.property
  have h01 := (hf x y z h).1
  have h12 := (hf x y z h).2
  have hp := (hf x z y h).1
  have h01' := congrFun h01 2
  have h12' := congrFun h12 2
  have hp' := congrFun hp 2
  have hv := congrFun h12 3
  simp [action01, action12] at h01' h12' hp' hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [action01] using congrFun h01 0
  · simpa [action12] using congrFun h12 0
  · simpa [action01, neg_eq_iff_eq_neg] using congrFun h01 1
  · simpa [action12, neg_eq_iff_eq_neg] using congrFun h12 1
  · exact h01'.symm
  · simpa [action12] using congrFun h12 3
  · linear_combination -h12' + h01' + hp' - hv

 /-- The component relations are sufficient as well as necessary; no additional
 local exchange equations are hidden in the component presentation. -/
theorem condition_iff_component_relations (f : Family q l) :
    Condition q l f ↔ ∀ x y z h,
      values q l f y x z h 0 = values q l f x y z h 0 ∧
      values q l f x z y h 0 = values q l f x y z h 0 ∧
      values q l f y x z h 1 = -values q l f x y z h 1 ∧
      values q l f x z y h 1 = -values q l f x y z h 1 ∧
      values q l f x y z h 2 = values q l f y x z h 3 ∧
      values q l f x z y h 3 = values q l f x y z h 3 ∧
      values q l f x y z h 3 + values q l f y x z h 3 +
        values q l f z x y h 3 = 0 := by
  constructor
  · intro hf
    exact component_relations q l ⟨f, (mem_residualSpace_iff q l f).mpr hf⟩
  · intro hf x y z h
    obtain ⟨ht01, ht12, hu01, hu12, hs, hv, hc⟩ := hf x y z h
    have hs01 := (hf y x z h).2.2.2.2.1
    have hs12 := (hf x z y h).2.2.2.2.1
    constructor
    · ext i
      fin_cases i <;> simp [action01]
      · exact ht01
      · linear_combination -hu01
      · exact hs.symm
      · exact hs01
    · ext i
      fin_cases i <;> simp [action12]
      · exact ht12
      · linear_combination -hu12
      · linear_combination -hs12 - hv - hc - hs
      · exact hv

section FiniteMixed
variable {n : ℕ} (b : Module.Basis (Fin n) ℂ Q)

/-- The finite mixed coordinate table at a supplied lepton input. -/
def mixedTable (f : residualSpace q l) (h : L) : TripleMixedCoordinates.space n :=
  ⟨fun i j k => values q l f.val (b i) (b j) (b k) h 3, by
    constructor
    · intro i j k
      exact (component_relations q l f (b i) (b j) (b k) h).2.2.2.2.2.1
    · intro i j k
      exact (component_relations q l f (b i) (b j) (b k) h).2.2.2.2.2.2⟩

def mixedCoordinates (f : residualSpace q l) (h : L) :
    TripleMixedCoordinates.Coordinates n :=
  TripleMixedCoordinates.equiv n (mixedTable q l b f h)

def flavorTable (f : residualSpace q l) (h : L) : TripleFlavorCoordinates.Space n :=
  (⟨fun i j k => values q l f.val (b i) (b j) (b k) h 0, by
    constructor
    · intro i j k; exact (component_relations q l f (b i) (b j) (b k) h).1
    · intro i j k; exact (component_relations q l f (b i) (b j) (b k) h).2.1⟩,
  (⟨fun i j k => values q l f.val (b i) (b j) (b k) h 1, by
    constructor
    · intro i j k; exact (component_relations q l f (b i) (b j) (b k) h).2.2.1
    · intro i j k; exact (component_relations q l f (b i) (b j) (b k) h).2.2.2.1⟩,
    mixedTable q l b f h))

def flavorCoordinates (f : residualSpace q l) (h : L) :
    TripleFlavorCoordinates.Coordinates n :=
  TripleFlavorCoordinates.equiv n (flavorTable q l b f h)

theorem flavorTable_ext {f g : residualSpace q l} {h : L}
    (hc : flavorCoordinates q l b f h = flavorCoordinates q l b g h) :
    flavorTable q l b f h = flavorTable q l b g h :=
  (TripleFlavorCoordinates.equiv n).injective hc

/-- These finite coordinates determine the actual residual coefficient, not
 just its local contraction at a selected gauge/spin probe. -/
theorem flavorCoordinates_injective {m : ℕ} (c : Module.Basis (Fin m) ℂ L)
    {f g : residualSpace q l}
    (hc : ∀ j, flavorCoordinates q l b f (c j) = flavorCoordinates q l b g (c j)) :
    f = g := by
  apply Subtype.ext
  funext r
  apply IntertwiningMap.ext
  apply ((b.tensorProduct b).tensorProduct (b.tensorProduct c)).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [Module.Basis.tensorProduct_apply]
  have hh := flavorTable_ext q l b (hc t)
  have ht := congrArg (fun a : TripleFlavorCoordinates.Space n => a.1.val i j k) hh
  have hu := congrArg (fun a : TripleFlavorCoordinates.Space n => a.2.1.val i j k) hh
  have hv := congrArg (fun a : TripleFlavorCoordinates.Space n => a.2.2.val i j k) hh
  have hv' := congrArg (fun a : TripleFlavorCoordinates.Space n => a.2.2.val j i k) hh
  fin_cases r
  · exact ht
  · exact hu
  · have hf := (component_relations q l f (b i) (b j) (b k) (c t)).2.2.2.2.1
    have hg := (component_relations q l g (b i) (b j) (b k) (c t)).2.2.2.2.1
    exact hf.trans (hv'.trans hg.symm)
  · exact hv

/-- All mixed basis evaluations are reconstructed from nonredundant indices. -/
theorem mixed_reconstruction (f : residualSpace q l) (h : L) (i j k : Fin n) :
    TripleMixedCoordinates.assemble (mixedCoordinates q l b f h) i j k =
      values q l f.val (b i) (b j) (b k) h 3 := by
  have hh := TripleMixedCoordinates.assemble_extract
    (mixedTable q l b f h).val (mixedTable q l b f h).property
  exact congrFun (congrFun (congrFun hh i) j) k

end FiniteMixed

end
end Physics.QqqlFlavorComponents
