import Physics.StandardModel.Operators.SMSparseCharacter

/-! Emit candidate slot data together with a kernel-checked equality.
The generator is not trusted; the generated theorem must build. -/
open GUT
def main : IO Unit := do
  let mut out := "import Physics.StandardModel.Operators.SMSparseCharacter\nnamespace GUT.SMKernelWeightData\nset_option autoImplicit false\ndef data : DeltaLOneSignedInput.Species → List SMSparseCharacter.Key\n"
  for s in (List.finRange 10 : List (Fin 10)) do
    out := out ++ s!"  | {(s : Fin 10).val} => [" ++
      String.intercalate "," ((SMSparseCharacter.weights s).map reprStr) ++ "]\n"
  out := out ++ "theorem weights_verified (s : DeltaLOneSignedInput.Species) : SMSparseCharacter.weights s = data s := by\n  fin_cases s <;> decide +kernel\n"
  out := out ++ "def tables := List.ofFn (fun s => Math.SparseWeightPolynomial.exteriorRows (data s))\ntheorem tables_verified : SMSparseCharacter.tables = tables := by\n  unfold SMSparseCharacter.tables tables\n  congr 1\n  funext s\n  rw [weights_verified]\nend GUT.SMKernelWeightData\n"
  IO.print out

#eval main
