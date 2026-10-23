import Math.RepresentationTheory.Content.GenerationTensorSupport
import Math.RepresentationTheory.Constructions.JointSourcePresentation

/-! Composition of proved core presentations with complete finite generation
occupation reduction. All occurrence tests are eliminated in favor of the
positive joint syntax. -/
namespace Math.JointContentPresentation
set_option autoImplicit false
noncomputable section
open Representation ExteriorContentTree JointSourcePresentation JointColorSpinWord

abbrev Cores : Content Group → Type
  | .leaf a => ∀ n, Presentation (a.rho.exteriorPower n)
  | .node l r => Cores l × Cores r

def indexed (k : ℕ) (a : Fin (k+1) → Leaf Group)
    (p : ∀ i, Presentation ((a i).rho.exteriorPower (a i).degree)) :
    Presentation (factor (IndexedExteriorContent.tree k a)) :=
  match k with
  | 0 => p 0
  | k+1 => tensor (p 0) (indexed k (fun i => a i.succ) (fun i => p i.succ))

def indexedCores (k : ℕ) (a : Fin (k+1) → Leaf Group)
    (p : ∀ i n, Presentation ((a i).rho.exteriorPower n)) :
    Cores (IndexedExteriorContent.tree k a) :=
  match k with
  | 0 => p 0
  | k+1 => (p 0,indexedCores k (fun i => a i.succ) (fun i => p i.succ))

def occupied : (t : Content Group) → Cores t → (c : GenerationTensorSupport.Choice t) →
    Presentation (factor (GenerationTensorSupport.occupied t c))
  | .leaf a, p, c => indexed 2 (fun i => { a with degree := (c.val i).val })
      (fun i => p (c.val i).val)
  | .node l r, p, c => tensor (occupied l p.1 c.1) (occupied r p.2 c.2)

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {z : Representation ℂ Group Z}

def Supports (t : Content Group) (p : Cores t) (q : Presentation z) : Prop :=
  ∃ c : GenerationTensorSupport.Choice t,
    JointSourceExpression.Supports (tensor (occupied t p c) q).expression

theorem allowed_iff (t : Content Group) (p : Cores t) (q : Presentation z) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((factor (GenerationTensorSupport.generations t)).tprod z)) ↔ Supports t p q := by
  rw [GenerationTensorSupport.allowed_iff]
  exact exists_congr (fun c => JointSourcePresentation.allowed_iff (tensor (occupied t p c) q))

end
end Math.JointContentPresentation
