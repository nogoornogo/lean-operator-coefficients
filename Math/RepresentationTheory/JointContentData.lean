import Math.RepresentationTheory.JointSourceData
import Math.RepresentationTheory.CompactGenerationOccupations
import Math.RepresentationTheory.JointContentPresentation

/-! Executable generation/species composition over numeric degrees. The
representation-valued tree appears only in the semantic correspondence. -/
namespace Math.JointContentData
set_option autoImplicit false
open JointSourceExpression ExteriorContentTree

abbrev Index : (k : Nat) → (Fin (k+1) → Nat) → Type
  | 0, d => CompactGenerationOccupations.Index (d 0)
  | k+1, d => CompactGenerationOccupations.Index (d 0) × Index k (fun i => d i.succ)

def generations (core : Nat → Expr) (n : Nat) (o : CompactGenerationOccupations.Index n) : Expr :=
  .tensor (core o.1.val) (.tensor (core o.2.val) (core (n-o.1.val-o.2.val)))

def occupied : (k : Nat) → (d : Fin (k+1) → Nat) →
    (Fin (k+1) → Nat → Expr) → Index k d → Expr
  | 0, d, core, o => generations (core 0) (d 0) o
  | k+1, d, core, o => .tensor (generations (core 0) (d 0) o.1)
      (occupied k (fun i => d i.succ) (fun i => core i.succ) o.2)

variable {G : Type} [Group G]

def choiceEquiv : (k : Nat) → (a : Fin (k+1) → Leaf G) →
    Index k (fun i => (a i).degree) ≃ GenerationTensorSupport.Choice (IndexedExteriorContent.tree k a)
  | 0, a => CompactGenerationOccupations.equiv (a 0).degree
  | k+1, a => Equiv.prodCongr (CompactGenerationOccupations.equiv (a 0).degree)
      (choiceEquiv k (fun i => a i.succ))

theorem generations_eq (a : Leaf JointColorSpinWord.Group)
    (p : ∀ n, JointSourcePresentation.Presentation (a.rho.exteriorPower n))
    (core : Nat → Expr) (hc : ∀ n, core n = (p n).expression)
    (o : CompactGenerationOccupations.Index a.degree) :
    generations core a.degree o =
      (JointContentPresentation.occupied (.leaf a) p
        (CompactGenerationOccupations.equiv a.degree o)).expression := by
  change Expr.tensor (core o.1.val) (Expr.tensor (core o.2.val)
      (core (a.degree-o.1.val-o.2.val))) = _
  rw [hc, hc, hc]
  rfl

theorem occupied_eq (k : Nat) (a : Fin (k+1) → Leaf JointColorSpinWord.Group)
    (p : ∀ i n, JointSourcePresentation.Presentation ((a i).rho.exteriorPower n))
    (core : Fin (k+1) → Nat → Expr) (hc : ∀ i n, core i n = (p i n).expression)
    (o : Index k (fun i => (a i).degree)) :
    occupied k (fun i => (a i).degree) core o =
      (JointContentPresentation.occupied (IndexedExteriorContent.tree k a)
        (JointContentPresentation.indexedCores k a p) (choiceEquiv k a o)).expression := by
  induction k with
  | zero => exact generations_eq (a 0) (p 0) (core 0) (hc 0) o
  | succ k ih =>
    change Expr.tensor (generations (core 0) (a 0).degree o.1)
      (occupied k (fun i => (a i.succ).degree) (fun i => core i.succ) o.2) = _
    rw [generations_eq (a 0) (p 0) (core 0) (hc 0) o.1]
    rw [ih (fun i => a i.succ) (fun i => p i.succ) (fun i => core i.succ)
      (fun i => hc i.succ) o.2]
    rfl

end Math.JointContentData
