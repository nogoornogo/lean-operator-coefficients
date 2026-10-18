import GUT.E6.Minuscule.D5Blocks
import Lean

/-!
Export the pinned input to the external exact-arithmetic experiment. Evaluation
here is data generation, not a proof or a trusted extension of the Lean kernel.
Run from the repository root with `lake env lean --run tools/e6/ExportMatrices.lean`.
-/

open TauCeti.DynkinType TauCeti.E6Minuscule GUT.E6.Minuscule Lean

private def entries (M : Matrix (Fin 27) (Fin 27) ℤ) : List (List ℤ) :=
  (List.finRange 27).flatMap fun a =>
    (List.finRange 27).filterMap fun b =>
      if M a b = 0 then none else some [a.val, b.val, M a b]

-- Weight-coordinate formulas avoid evaluating the partial-equivalence carrier.
private def raisingEntries (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  fun a b => if e6MinusculeWeight b i = -1 ∧
    ∀ k, e6MinusculeWeight a k = e6MinusculeWeight b k + CartanMatrix.E 6 i k then 1 else 0

private def loweringEntries (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  fun a b => if e6MinusculeWeight b i = 1 ∧
    ∀ k, e6MinusculeWeight a k = e6MinusculeWeight b k - CartanMatrix.E 6 i k then 1 else 0

example (i : Fin 6) : raisingEntries i = raisingMatrix i := by
  decide +kernel +revert

example (i : Fin 6) : loweringEntries i = loweringMatrix i := by
  decide +kernel +revert

def main : IO Unit := do
  IO.eprintln "E6 candidate export: weights"
  let weights := toJson (List.ofFn fun a => List.ofFn (e6MinusculeWeight a))
  IO.eprintln s!"E6 candidate export: {weights.compress.length} weight bytes; grading"
  let grades := toJson (List.ofFn grade)
  IO.eprintln s!"E6 candidate export: {grades.compress.length} grade bytes; raising"
  let raising := toJson (List.ofFn fun i => entries (raisingEntries i))
  IO.eprintln s!"E6 candidate export: {raising.compress.length} raising bytes; lowering"
  let lowering := toJson (List.ofFn fun i => entries (loweringEntries i))
  IO.eprintln s!"E6 candidate export: {lowering.compress.length} lowering bytes; diagonal"
  let diagonal := toJson (List.ofFn fun i => entries (cartanGeneratorMatrix i))
  IO.eprintln s!"E6 candidate export: {diagonal.compress.length} diagonal bytes; output"
  IO.println <| (Json.mkObj [
    ("schema", toJson (1 : Nat)), ("weights", weights),
    ("d5_nodes", toJson (List.ofFn fun i => (d5Node i).val)),
    ("grades", grades), ("raising", raising), ("lowering", lowering), ("diagonal", diagonal)
    ]).compress
