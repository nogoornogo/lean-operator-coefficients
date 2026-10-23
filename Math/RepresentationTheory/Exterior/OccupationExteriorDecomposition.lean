import Math.RepresentationTheory.Exterior.FiniteExteriorExhaustion
import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.RepresentationTheory.Decomposition.FiniteBlockHom

/-! Complete equivariant occupation decomposition of a homogeneous exterior
power. Actual species projections, their cross vanishing and symbolic
occupation exhaustion give both inverse maps. No basis is expanded. -/
namespace Math.OccupationExteriorDecomposition
set_option autoImplicit false
noncomputable section
open Representation PatternExteriorSource FiniteExteriorExhaustion
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (n : ℕ)
abbrev Index := Occupation (S := S) n
local instance : Fintype (Index (S := S) n) := Fintype.ofFinite _
local instance : DecidableEq (Index (S := S) n) := Classical.decEq _
abbrev pattern (c : Index (S := S) n) := representative n c
abbrev block (c : Index (S := S) n) := representation r (pattern n c)
abbrev Carrier (c : Index (S := S) n) : Type _ := Source r (pattern n c)
abbrev source := Full r (n := n)
abbrev target := FiniteBlockHom.action (block r n)

theorem projection_other (c d : Index (S := S) n) (hcd : c≠d) (x : Carrier r n d) :
    projectionLinear r (pattern n c) x.val=0 := by
  obtain ⟨y, rfl⟩ := onto_surjective r (pattern n d) x
  have h : (projectionLinear r (pattern n c)).comp (PatternExteriorSource.map r (pattern n d)).toLinearMap=0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PatternExteriorSource.map, PiTensorProduct.lift.tprod, LinearMap.zero_apply]
    change projectionLinear r (pattern n c)
      (exteriorPower.ιMulti ℂ n (fun i => Pi.single (pattern n d i) (v i)))=0
    apply projection_vanish
    intro he
    have hh := (orbit_iff_counts (p := pattern n c) (pattern n d)).mp he
    apply hcd
    apply Subtype.ext
    funext s
    apply Fin.ext
    have hc := congrArg Fin.val (congrFun (representative_counts n c) s)
    have hd := congrArg Fin.val (congrFun (representative_counts n d) s)
    exact hc.symm.trans ((hh s).symm.trans hd)
  exact LinearMap.congr_fun h y

def forward : IntertwiningMap (source r n) (target r n) where
  toLinearMap := LinearMap.pi (fun c => (projection r (pattern n c)).toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext c
    exact (projection r (pattern n c)).isIntertwining _ _ g x

def backward : IntertwiningMap (target r n) (source r n) :=
  DistinctIrreducibleAssembly.assemble (A := Carrier r n)
    (B := ⋀[ℂ]^n (∀ s, V s)) (block r n) (source r n)
    (fun c => inclusion r (pattern n c))

theorem forward_inclusion (c : Index (S := S) n) (x : Carrier r n c) :
    forward r n (inclusion r (pattern n c) x)=(Pi.single c x : ∀ d, Carrier r n d) := by
  funext d
  change projectionLinear r (pattern n d) x.val=(Pi.single c x : ∀ d, Carrier r n d) d
  by_cases hdc : d=c
  · subst d
    rw [projection_inclusion, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hdc]
    exact projection_other r n d c hdc x

theorem backward_single (c : Index (S := S) n) (x : Carrier r n c) :
    backward r n (Pi.single c x)=inclusion r (pattern n c) x :=
  DistinctIrreducibleAssembly.assemble_single (A := Carrier r n)
    (B := ⋀[ℂ]^n (∀ s, V s)) (block r n) (source r n)
      (fun c => inclusion r (pattern n c)) c x

theorem backward_forward (x : ⋀[ℂ]^n (∀ s, V s)) : backward r n (forward r n x)=x := by
  have h : (backward r n).comp (forward r n)=IntertwiningMap.id (source r n) := by
    apply occupation_ext r n (source r n)
    intro c
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    change backward r n (forward r n (inclusion r (pattern n c) y))=inclusion r (pattern n c) y
    rw [forward_inclusion, backward_single]
  exact DFunLike.congr_fun h x

theorem forward_backward (x : ∀ c, Carrier r n c) : forward r n (backward r n x)=x := by
  rw [backward, DistinctIrreducibleAssembly.assemble_apply]
  rw [map_sum]
  simp only [forward_inclusion]
  ext c
  simp

/-- Complete occupation decomposition of the actual homogeneous exterior
representation, preserving every group factor. -/
def equivalence : Representation.Equiv (source r n) (target r n) where
  toLinearEquiv :=
    { toLinearMap := (forward r n).toLinearMap
      invFun := backward r n
      left_inv := backward_forward r n
      right_inv := forward_backward r n }
  isIntertwining' := (forward r n).isIntertwining'

end
end Math.OccupationExteriorDecomposition
