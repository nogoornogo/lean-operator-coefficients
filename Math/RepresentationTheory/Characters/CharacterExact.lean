import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Trace.Exact

/-!
# Characters along exact sequences

The character is additive along a short exact sequence of representations.
For an intertwiner, subtracting the kernel/range and range/cokernel identities
gives the kernel-minus-cokernel character index. The cokernel is the algebraic
quotient by the range. No invariant complement, unitarity, semisimplicity,
topology, or finiteness of the acting monoid is assumed.
-/

namespace Math.CharacterExact

noncomputable section

variable {k G : Type*} [Field k] [Monoid G]
variable {N V W : Type*}
variable [AddCommGroup N] [Module k N]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Additivity of characters needs only exactness and finite dimension of
the middle representation, not an equivariant splitting. -/
theorem character_eq_add_of_exact [FiniteDimensional k V]
    {rhoN : Representation k G N} {rhoV : Representation k G V}
    {rhoW : Representation k G W}
    (i : rhoN.IntertwiningMap rhoV) (p : rhoV.IntertwiningMap rhoW)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (g : G) :
    rhoV.character g = rhoN.character g + rhoW.character g :=
  LinearMap.trace_eq_add_of_exact hi hp hex (i.isIntertwining' g).symm (p.isIntertwining' g)

variable {rho : Representation k G V}

/-- The action on the algebraic quotient by an invariant subspace. -/
def quotientRepresentation (S : Subrepresentation rho) :
    Representation k G (V ⧸ S.toSubmodule) :=
  rho.quotient S.toSubmodule (fun g _ hx => S.apply_mem_toSubmodule g hx)

def subtypeIntertwiner (S : Subrepresentation rho) :
    S.toRepresentation.IntertwiningMap rho where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

def quotientProjection (S : Subrepresentation rho) :
    rho.IntertwiningMap (quotientRepresentation S) where
  toLinearMap := S.toSubmodule.mkQ
  isIntertwining' _ := rfl

/-- The subrepresentation/quotient character identity, without semisimplicity. -/
theorem character_eq_sub_add_quotient [FiniteDimensional k V]
    (S : Subrepresentation rho) (g : G) :
    rho.character g = S.toRepresentation.character g + (quotientRepresentation S).character g :=
  character_eq_add_of_exact (subtypeIntertwiner S) (quotientProjection S)
    Subtype.val_injective S.toSubmodule.mkQ_surjective
    (LinearMap.exact_subtype_mkQ S.toSubmodule) g

/-- Any invariant complement gives an actual representation equivalence to
the quotient, via the canonical quotient map on that complement. -/
def complementQuotientEquiv (S T : Subrepresentation rho)
    (h : IsCompl S.toSubmodule T.toSubmodule) :
    Representation.Equiv T.toRepresentation (quotientRepresentation S) :=
  .mk (S.toSubmodule.quotientEquivOfIsCompl T.toSubmodule h).symm (by
    intro g
    apply LinearMap.ext
    intro x
    rfl)

variable {rhoV : Representation k G V} {rhoW : Representation k G W}

def rangeRestrict (f : rhoV.IntertwiningMap rhoW) :
    rhoV.IntertwiningMap f.range.toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rhoV rhoW f g x

/-- The cokernel carries its induced action, with no choice of a complement. -/
def cokernelRepresentation (f : rhoV.IntertwiningMap rhoW) :
    Representation k G (W ⧸ f.range.toSubmodule) :=
  quotientRepresentation f.range

theorem character_eq_kernel_add_range [FiniteDimensional k V]
    (f : rhoV.IntertwiningMap rhoW) (g : G) :
    rhoV.character g = f.ker.toRepresentation.character g + f.range.toRepresentation.character g := by
  apply character_eq_add_of_exact (subtypeIntertwiner f.ker) (rangeRestrict f)
    Subtype.val_injective
  · exact LinearMap.range_eq_top.mp f.toLinearMap.range_rangeRestrict
  · apply LinearMap.exact_iff.mpr
    change LinearMap.ker f.toLinearMap.rangeRestrict =
      LinearMap.range f.ker.toSubmodule.subtype
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    rfl

/-- The algebraic unmatched index, defined independently of the mass-map
interpretation and of any inner product on source or target. -/
def indexCharacter (f : rhoV.IntertwiningMap rhoW) (g : G) : k :=
  f.ker.toRepresentation.character g - (cokernelRepresentation f).character g

/-- Removing an equivariantly paired range preserves the character difference. -/
theorem indexCharacter_eq_source_sub_target
    [FiniteDimensional k V] [FiniteDimensional k W]
    (f : rhoV.IntertwiningMap rhoW) (g : G) :
    indexCharacter f g = rhoV.character g - rhoW.character g := by
  have hV := character_eq_kernel_add_range f g
  have hW := character_eq_sub_add_quotient f.range g
  rw [hV, hW]
  unfold indexCharacter cokernelRepresentation
  abel

end

end Math.CharacterExact
