import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockAssembly

namespace Physics.LiSixQuarkBlockExtraction
noncomputable section
open LiSixQuarkBlockAssembly LiSixQuarkBlockSolvers LiSixQuarkPairBlock

def pack22 (c : Array) : Fin 4 → ℂ := ![c 0 0,c 0 1,c 1 0,c 1 1]
def pack23 (c : Array) : Fin 6 → ℂ := ![c 0 2,c 0 3,c 0 4,c 1 2,c 1 3,c 1 4]
def pack32 (c : Array) : Fin 6 → ℂ := ![c 2 0,c 2 1,c 3 0,c 3 1,c 4 0,c 4 1]
def pack33 (c : Array) : Fin 9 → ℂ :=
  ![c 2 2,c 2 3,c 2 4,c 3 2,c 3 3,c 3 4,c 4 2,c 4 3,c 4 4]

theorem pack22_presentation (v : Fin 25 → ℂ) : pack22 (presentation v) = y22 v := by
  ext i; fin_cases i <;> rfl
theorem pack23_presentation (v : Fin 25 → ℂ) : pack23 (presentation v) = y23 v := by
  ext i; fin_cases i <;> rfl
theorem pack32_presentation (v : Fin 25 → ℂ) : pack32 (presentation v) = y32 v := by
  ext i; fin_cases i <;> rfl
theorem pack33_presentation (v : Fin 25 → ℂ) : pack33 (presentation v) = y33 v := by
  ext i; fin_cases i <;> rfl

/-- Extract triples independently, then undo the visible sum/difference couplings. -/
def decodeBlocks (x : Fin 4 → ℂ) (y z : Fin 6 → ℂ) (w : Fin 9 → ℂ) : Fin 25 → ℂ :=
  let a := first32 z
  let d := difference32 z
  let b := first23 y
  let s := sum23 y
  let h := first33 w
  let l := last33 w
  let f := pair33 w
  let q := scalar33 w
  let t := traceCoefficient (x 0) (x 3)
  let r := alternatingCoefficient (x 0) (x 1) (x 2) (x 3)
  let u := standardFirst (x 0) (x 1) (x 3)
  let v := standardSecond (x 0) (x 2) (x 3)
  ![a 0,a 1,a 2, b 0-a 0/2,b 1-a 1/2,b 2-a 2/2,
    (s 0+d 0)/2,(s 1+d 1)/2,(s 2+d 2)/2,
    (s 0-d 0)/2,(s 1-d 1)/2,(s 2-d 2)/2,
    (r+q)/2,(r-q)/2,h 0,h 1,h 2,u-2*f 0,v-2*f 1,f 0,f 1,l 0,l 1,l 2,t]

def decode (c : Array) : Fin 25 → ℂ :=
  decodeBlocks (pack22 c) (pack23 c) (pack32 c) (pack33 c)

theorem trace22_forward (v : Fin 25 → ℂ) :
    traceCoefficient (y22 v 0) (y22 v 3) = v 24 := by
  simp [y22, traceCoefficient]
theorem alternating22_forward (v : Fin 25 → ℂ) :
    alternatingCoefficient (y22 v 0) (y22 v 1) (y22 v 2) (y22 v 3) = v 12+v 13 := by
  simp [y22, alternatingCoefficient]; ring
theorem standardFirst22_forward (v : Fin 25 → ℂ) :
    standardFirst (y22 v 0) (y22 v 1) (y22 v 3) = v 17+2*v 19 := by
  simp [y22, standardFirst]; ring
theorem standardSecond22_forward (v : Fin 25 → ℂ) :
    standardSecond (y22 v 0) (y22 v 2) (y22 v 3) = v 18+2*v 20 := by
  simp [y22, standardSecond]; ring

/-- Reconstruction is assembled from proved block identities, not 625 scalar
entries of a proposed inverse matrix. -/
theorem decode_presentation (v : Fin 25 → ℂ) : decode (presentation v) = v := by
  unfold decode
  rw [pack22_presentation, pack23_presentation, pack32_presentation, pack33_presentation]
  simp only [decodeBlocks, y23, y32, y33, first32_forward, difference32_forward,
    first23_forward, sum23_forward, scalar33_forward, first33_forward, pair33_forward,
    last33_forward, trace22_forward, alternating22_forward,
    standardFirst22_forward, standardSecond22_forward]
  ext i
  fin_cases i <;> simp [a32, d32, a23, s23, h33, s33, l33]

/-- The original selected assembly has a symbolic left inverse. -/
theorem decode_original (v : Fin 25 → ℂ) : decode (entries (originalAssembly v)) = v := by
  rw [presentation_correct, decode_presentation]

private theorem entries_smul_row0 (z : ℂ) (c : Array) (q : Fin 5) :
    entries (z • c) 0 q = z * entries c 0 q := by
  fin_cases q <;> simp [entries, colorEntries] <;> ring

private theorem entries_smul_row1 (z : ℂ) (c : Array) (q : Fin 5) :
    entries (z • c) 1 q = z * entries c 1 q := by
  fin_cases q <;> simp [entries, colorEntries] <;> ring

private theorem entries_smul_row2 (z : ℂ) (c : Array) (q : Fin 5) :
    entries (z • c) 2 q = z * entries c 2 q := by
  fin_cases q <;> simp [entries, colorEntries] <;> ring

private theorem entries_smul_row3 (z : ℂ) (c : Array) (q : Fin 5) :
    entries (z • c) 3 q = z * entries c 3 q := by
  fin_cases q <;> simp [entries, colorEntries] <;> ring

private theorem entries_smul_row4 (z : ℂ) (c : Array) (q : Fin 5) :
    entries (z • c) 4 q = z * entries c 4 q := by
  fin_cases q <;> simp [entries, colorEntries] <;> ring

def entriesLinear : Array →ₗ[ℂ] Array where
  toFun := entries
  map_add' c d := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [entries, colorEntries] <;> ring
  map_smul' z c := by
    ext p q
    fin_cases p
    · exact entries_smul_row0 z c q
    · exact entries_smul_row1 z c q
    · exact entries_smul_row2 z c q
    · exact entries_smul_row3 z c q
    · exact entries_smul_row4 z c q

/-- Scalar-coordinate bookkeeping is split to retain the default proof budgets. -/
private theorem decode_linear_0 (c d : Array) (z : ℂ) :
    decode (c + d) 0 = decode c 0 + decode d 0 ∧
    decode (z • c) 0 = z * decode c 0 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_1 (c d : Array) (z : ℂ) :
    decode (c + d) 1 = decode c 1 + decode d 1 ∧
    decode (z • c) 1 = z * decode c 1 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_2 (c d : Array) (z : ℂ) :
    decode (c + d) 2 = decode c 2 + decode d 2 ∧
    decode (z • c) 2 = z * decode c 2 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_3 (c d : Array) (z : ℂ) :
    decode (c + d) 3 = decode c 3 + decode d 3 ∧
    decode (z • c) 3 = z * decode c 3 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_4 (c d : Array) (z : ℂ) :
    decode (c + d) 4 = decode c 4 + decode d 4 ∧
    decode (z • c) 4 = z * decode c 4 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_5 (c d : Array) (z : ℂ) :
    decode (c + d) 5 = decode c 5 + decode d 5 ∧
    decode (z • c) 5 = z * decode c 5 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_6 (c d : Array) (z : ℂ) :
    decode (c + d) 6 = decode c 6 + decode d 6 ∧
    decode (z • c) 6 = z * decode c 6 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_7 (c d : Array) (z : ℂ) :
    decode (c + d) 7 = decode c 7 + decode d 7 ∧
    decode (z • c) 7 = z * decode c 7 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_8 (c d : Array) (z : ℂ) :
    decode (c + d) 8 = decode c 8 + decode d 8 ∧
    decode (z • c) 8 = z * decode c 8 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_9 (c d : Array) (z : ℂ) :
    decode (c + d) 9 = decode c 9 + decode d 9 ∧
    decode (z • c) 9 = z * decode c 9 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_10 (c d : Array) (z : ℂ) :
    decode (c + d) 10 = decode c 10 + decode d 10 ∧
    decode (z • c) 10 = z * decode c 10 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_11 (c d : Array) (z : ℂ) :
    decode (c + d) 11 = decode c 11 + decode d 11 ∧
    decode (z • c) 11 = z * decode c 11 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_12 (c d : Array) (z : ℂ) :
    decode (c + d) 12 = decode c 12 + decode d 12 ∧
    decode (z • c) 12 = z * decode c 12 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_13 (c d : Array) (z : ℂ) :
    decode (c + d) 13 = decode c 13 + decode d 13 ∧
    decode (z • c) 13 = z * decode c 13 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_14 (c d : Array) (z : ℂ) :
    decode (c + d) 14 = decode c 14 + decode d 14 ∧
    decode (z • c) 14 = z * decode c 14 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_15 (c d : Array) (z : ℂ) :
    decode (c + d) 15 = decode c 15 + decode d 15 ∧
    decode (z • c) 15 = z * decode c 15 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_16 (c d : Array) (z : ℂ) :
    decode (c + d) 16 = decode c 16 + decode d 16 ∧
    decode (z • c) 16 = z * decode c 16 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_17 (c d : Array) (z : ℂ) :
    decode (c + d) 17 = decode c 17 + decode d 17 ∧
    decode (z • c) 17 = z * decode c 17 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_18 (c d : Array) (z : ℂ) :
    decode (c + d) 18 = decode c 18 + decode d 18 ∧
    decode (z • c) 18 = z * decode c 18 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_19 (c d : Array) (z : ℂ) :
    decode (c + d) 19 = decode c 19 + decode d 19 ∧
    decode (z • c) 19 = z * decode c 19 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_20 (c d : Array) (z : ℂ) :
    decode (c + d) 20 = decode c 20 + decode d 20 ∧
    decode (z • c) 20 = z * decode c 20 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_21 (c d : Array) (z : ℂ) :
    decode (c + d) 21 = decode c 21 + decode d 21 ∧
    decode (z • c) 21 = z * decode c 21 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_22 (c d : Array) (z : ℂ) :
    decode (c + d) 22 = decode c 22 + decode d 22 ∧
    decode (z • c) 22 = z * decode c 22 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_23 (c d : Array) (z : ℂ) :
    decode (c + d) 23 = decode c 23 + decode d 23 ∧
    decode (z • c) 23 = z * decode c 23 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

private theorem decode_linear_24 (c d : Array) (z : ℂ) :
    decode (c + d) 24 = decode c 24 + decode d 24 ∧
    decode (z • c) 24 = z * decode c 24 := by
  constructor <;> simp [decode, decodeBlocks, pack22, pack23, pack32, pack33, first32, difference32, first23, sum23, scalar33, first33, pair33, last33, traceCoefficient, alternatingCoefficient, standardFirst, standardSecond] <;> ring

def decodeLinear : Array →ₗ[ℂ] (Fin 25 → ℂ) where
  toFun := decode
  map_add' c d := by
    ext i
    fin_cases i
    · exact (decode_linear_0 c d 0).1
    · exact (decode_linear_1 c d 0).1
    · exact (decode_linear_2 c d 0).1
    · exact (decode_linear_3 c d 0).1
    · exact (decode_linear_4 c d 0).1
    · exact (decode_linear_5 c d 0).1
    · exact (decode_linear_6 c d 0).1
    · exact (decode_linear_7 c d 0).1
    · exact (decode_linear_8 c d 0).1
    · exact (decode_linear_9 c d 0).1
    · exact (decode_linear_10 c d 0).1
    · exact (decode_linear_11 c d 0).1
    · exact (decode_linear_12 c d 0).1
    · exact (decode_linear_13 c d 0).1
    · exact (decode_linear_14 c d 0).1
    · exact (decode_linear_15 c d 0).1
    · exact (decode_linear_16 c d 0).1
    · exact (decode_linear_17 c d 0).1
    · exact (decode_linear_18 c d 0).1
    · exact (decode_linear_19 c d 0).1
    · exact (decode_linear_20 c d 0).1
    · exact (decode_linear_21 c d 0).1
    · exact (decode_linear_22 c d 0).1
    · exact (decode_linear_23 c d 0).1
    · exact (decode_linear_24 c d 0).1
  map_smul' z c := by
    ext i
    fin_cases i
    · exact (decode_linear_0 c 0 z).2
    · exact (decode_linear_1 c 0 z).2
    · exact (decode_linear_2 c 0 z).2
    · exact (decode_linear_3 c 0 z).2
    · exact (decode_linear_4 c 0 z).2
    · exact (decode_linear_5 c 0 z).2
    · exact (decode_linear_6 c 0 z).2
    · exact (decode_linear_7 c 0 z).2
    · exact (decode_linear_8 c 0 z).2
    · exact (decode_linear_9 c 0 z).2
    · exact (decode_linear_10 c 0 z).2
    · exact (decode_linear_11 c 0 z).2
    · exact (decode_linear_12 c 0 z).2
    · exact (decode_linear_13 c 0 z).2
    · exact (decode_linear_14 c 0 z).2
    · exact (decode_linear_15 c 0 z).2
    · exact (decode_linear_16 c 0 z).2
    · exact (decode_linear_17 c 0 z).2
    · exact (decode_linear_18 c 0 z).2
    · exact (decode_linear_19 c 0 z).2
    · exact (decode_linear_20 c 0 z).2
    · exact (decode_linear_21 c 0 z).2
    · exact (decode_linear_22 c 0 z).2
    · exact (decode_linear_23 c 0 z).2
    · exact (decode_linear_24 c 0 z).2

def reindex : (Fin 25 → ℂ) →ₗ[ℂ] Array where
  toFun v p q := v ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Hierarchical extraction as an actual linear map, ready for matrix transport. -/
def extraction : (Fin 25 → ℂ) →ₗ[ℂ] (Fin 25 → ℂ) :=
  (decodeLinear.comp entriesLinear).comp reindex

end
end Physics.LiSixQuarkBlockExtraction
