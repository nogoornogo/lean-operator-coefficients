import Math.RepresentationTheory.Fields.DerivativeConnection
import Math.RepresentationTheory.Jets.JetFunctor
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

/-! A constant field dictionary induces the actual mixed jet-algebra map.
The same supplied direction action is retained; relation preimages are taken
only after the complete interacting input has been generated. -/
namespace Math.FieldJetConnection
set_option autoImplicit false
noncomputable section
open Representation JetDirections
open scoped TensorProduct
variable {H F B F' B' I : Type*} [Group H]
  {r : Representation ℂ H (JetLinear.Field F)}
  {s : Representation ℂ H (JetLinear.Field F')}

def jets (e : IntertwiningMap r s) (d : Representation ℂ H (Direction I)) :
    IntertwiningMap (combined r d) (combined s d) where
  toLinearMap := JetLinear.map e.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change ((JetLinear.map e.toLinearMap).comp (JetLinear.map (r g))) (jetMap (d g) v) =
      JetLinear.map (s g) (jetMap (d g) (JetLinear.map e.toLinearMap v))
    rw [← JetLinear.map_comp, e.isIntertwining', JetLinear.map_comp, internal_commute]
    rfl

def jetsEquiv (e : Representation.Equiv r s) (d : Representation ℂ H (Direction I)) :
    Representation.Equiv (combined r d) (combined s d) :=
  .mk
    (LinearEquiv.ofLinearMap (jets e.toIntertwiningMap d).toLinearMap
      (jets e.symm.toIntertwiningMap d).toLinearMap
      (by
        change (JetLinear.map e.toLinearMap).comp (JetLinear.map e.symm.toLinearMap) = LinearMap.id
        rw [← JetLinear.map_comp, FieldSelection.equiv_comp_symm e, JetLinear.map_id])
      (by
        change (JetLinear.map e.symm.toLinearMap).comp (JetLinear.map e.toLinearMap) = LinearMap.id
        rw [← JetLinear.map_comp, FieldSelection.equiv_symm_comp e, JetLinear.map_id]))
    (jets e.toIntertwiningMap d).isIntertwining'

section Algebra
variable {a : Representation ℂ H (JetLinear.Jet F I)}
  {a' : Representation ℂ H (JetLinear.Jet F' I)}
  {b : Representation ℂ H (JetLinear.Jet B I)}
  {b' : Representation ℂ H (JetLinear.Jet B' I)}

def odd (e : IntertwiningMap a a') :
    IntertwiningMap a.exteriorAlgebra a'.exteriorAlgebra where
  toLinearMap := (ExteriorAlgebra.map e.toLinearMap).toLinearMap
  isIntertwining' g := by
    have h : (ExteriorAlgebra.map e.toLinearMap).comp (ExteriorAlgebra.map (a g)) =
        (ExteriorAlgebra.map (a' g)).comp (ExteriorAlgebra.map e.toLinearMap) := by
      rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, e.isIntertwining']
    exact congrArg AlgHom.toLinearMap h

def even (e : IntertwiningMap b b') :
    IntertwiningMap (JetFunctor.polynomialAction b) (JetFunctor.polynomialAction b') where
  toLinearMap := (JetFunctor.polynomialMap e.toLinearMap).toLinearMap
  isIntertwining' g := by
    have h : (JetFunctor.polynomialMap e.toLinearMap).comp (JetFunctor.polynomialMap (b g)) =
        (JetFunctor.polynomialMap (b' g)).comp (JetFunctor.polynomialMap e.toLinearMap) := by
      rw [← JetFunctor.polynomialMap_comp, ← JetFunctor.polynomialMap_comp, e.isIntertwining']
    exact congrArg AlgHom.toLinearMap h

def mixed (e : IntertwiningMap a a') (f : IntertwiningMap b b') :
    IntertwiningMap (JetFunctor.mixedAction a b) (JetFunctor.mixedAction a' b') :=
  (odd e).tensor (even f)

@[simp] theorem mixed_odd (e : IntertwiningMap a a') (f : IntertwiningMap b b')
    (v : JetLinear.Jet F I) : mixed e f (JetFunctor.oddVector v) =
      JetFunctor.oddVector (e v) := by
  change TensorProduct.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap
    (JetFunctor.polynomialMap f.toLinearMap).toLinearMap ((ExteriorAlgebra.ι ℂ) v ⊗ₜ[ℂ] 1) = _
  simp [JetFunctor.oddVector]

@[simp] theorem mixed_even (e : IntertwiningMap a a') (f : IntertwiningMap b b')
    (v : JetLinear.Jet B I) : mixed e f (JetFunctor.evenVector v) =
      JetFunctor.evenVector (f v) := by
  change TensorProduct.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap
    (JetFunctor.polynomialMap f.toLinearMap).toLinearMap (1 ⊗ₜ[ℂ] JetLinear.linearForm v) = _
  simp [JetFunctor.evenVector, JetFunctor.polynomialMap_linearForm]

def oddEquiv (e : Representation.Equiv a a') :
    Representation.Equiv a.exteriorAlgebra a'.exteriorAlgebra :=
  .mk
    (LinearEquiv.ofLinearMap (odd e.toIntertwiningMap).toLinearMap
      (odd e.symm.toIntertwiningMap).toLinearMap
      (by
        have h : (ExteriorAlgebra.map e.toLinearMap).comp (ExteriorAlgebra.map e.symm.toLinearMap) =
            AlgHom.id ℂ _ := by
          rw [ExteriorAlgebra.map_comp_map, FieldSelection.equiv_comp_symm e, ExteriorAlgebra.map_id]
        exact congrArg AlgHom.toLinearMap h)
      (by
        have h : (ExteriorAlgebra.map e.symm.toLinearMap).comp (ExteriorAlgebra.map e.toLinearMap) =
            AlgHom.id ℂ _ := by
          rw [ExteriorAlgebra.map_comp_map, FieldSelection.equiv_symm_comp e, ExteriorAlgebra.map_id]
        exact congrArg AlgHom.toLinearMap h))
    (odd e.toIntertwiningMap).isIntertwining'

def evenEquiv (e : Representation.Equiv b b') :
    Representation.Equiv (JetFunctor.polynomialAction b) (JetFunctor.polynomialAction b') :=
  .mk
    (LinearEquiv.ofLinearMap (even e.toIntertwiningMap).toLinearMap
      (even e.symm.toIntertwiningMap).toLinearMap
      (by
        have h : (JetFunctor.polynomialMap e.toLinearMap).comp
            (JetFunctor.polynomialMap e.symm.toLinearMap) = AlgHom.id ℂ _ := by
          rw [← JetFunctor.polynomialMap_comp, FieldSelection.equiv_comp_symm e, JetFunctor.polynomialMap_id]
        exact congrArg AlgHom.toLinearMap h)
      (by
        have h : (JetFunctor.polynomialMap e.symm.toLinearMap).comp
            (JetFunctor.polynomialMap e.toLinearMap) = AlgHom.id ℂ _ := by
          rw [← JetFunctor.polynomialMap_comp, FieldSelection.equiv_symm_comp e, JetFunctor.polynomialMap_id]
        exact congrArg AlgHom.toLinearMap h))
    (even e.toIntertwiningMap).isIntertwining'

def mixedEquiv (e : Representation.Equiv a a') (f : Representation.Equiv b b') :
    Representation.Equiv (JetFunctor.mixedAction a b) (JetFunctor.mixedAction a' b') :=
  ExternalInvariantTensor.tensorEquiv (oddEquiv e) (evenEquiv f)
end Algebra

variable {rB : Representation ℂ H (JetLinear.Field B)}
  {sB : Representation ℂ H (JetLinear.Field B')}

def fields (e : IntertwiningMap r s) (f : IntertwiningMap rB sB)
    (d : Representation ℂ H (Direction I)) := mixed (jets e d) (jets f d)

def fieldEquiv (e : Representation.Equiv r s) (f : Representation.Equiv rB sB)
    (d : Representation ℂ H (Direction I)) := mixedEquiv (jetsEquiv e d) (jetsEquiv f d)

/-- The caller supplies only the generator dictionary and direction action.
This theorem verifies their compatibility at every derivative order. -/
theorem generator (e : IntertwiningMap r s) (f : IntertwiningMap rB sB)
    (d : Representation ℂ H (Direction I)) (v : JetLinear.Field F) (alpha : I →₀ ℕ) :
    fields e f d (JetFunctor.oddVector (JetLinear.atOrder alpha v)) =
      JetFunctor.oddVector (JetLinear.atOrder alpha (e v)) := by
  rw [fields, mixed_odd]
  exact congrArg JetFunctor.oddVector (JetLinear.map_atOrder e.toLinearMap alpha v)

section Coordinates
variable {U V S T : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]

/-- Coordinate syntax for an actual representation. A basis is a presentation
choice, not a spectrum or symmetry hypothesis. -/
def coordinateAction (a : Representation ℂ H U) (b : Module.Basis S ℂ U) :
    Representation ℂ H (JetLinear.Field S) := b.repr.conjRingEquiv.toMonoidHom.comp a

def coordinates (a : Representation ℂ H U) (b : Module.Basis S ℂ U) :
    Representation.Equiv a (coordinateAction a b) :=
  .mk b.repr (by
    intro g
    apply LinearMap.ext
    intro u
    change b.repr (a g u) = b.repr (a g (b.repr.symm (b.repr u)))
    rw [b.repr.symm_apply_apply])

def dictionaryInCoordinates {a : Representation ℂ H U} {b : Representation ℂ H V}
    (e : Representation.Equiv a b) (u : Module.Basis S ℂ U) (v : Module.Basis T ℂ V) :=
  (coordinates a u).symm.trans (e.trans (coordinates b v))

def coordinateJets {a : Representation ℂ H U} {b : Representation ℂ H V}
    (e : Representation.Equiv a b) (u : Module.Basis S ℂ U) (v : Module.Basis T ℂ V)
    (d : Representation ℂ H (Direction I)) :=
  fieldEquiv (dictionaryInCoordinates e u v)
    (Representation.Equiv.refl (Representation.trivial ℂ H (JetLinear.Field Unit))) d
end Coordinates

end
end Math.FieldJetConnection
