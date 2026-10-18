import Physics.StandardModel.Operators.HeeckLeSixQuarkCouplingConnection

/-! Extraction by the color-pair quotient, five residual scalar equations and
up-even/up-odd pair coordinates. The proof uses the established source/block
identities as interfaces, without unfolding a 25-dimensional inverse table. -/
namespace GUT.HeeckLeSixQuarkExtraction
noncomputable section
open LiSixQuarkLocalAction HeeckLeSixQuarkAssemblyBase HeeckLeSixQuarkPairCoordinates
open HeeckLeSixQuarkPairSolvers HeeckLeSixQuarkPairConnection
open HeeckLeSixQuarkQuotientConnection HeeckLeSixQuarkCouplingConnection
variable {K : Type*} [Field K] [CharZero K]

attribute [local irreducible] HeeckLeSixQuarkBlocks.orbit assemble source0Assembly
  source1Assembly evenAssembly oddAssembly couplingAssembly
  HeeckLeSixQuarkQuotient.sectionMap HeeckLeSixQuarkQuotient.forward

def remainder : Arr (K := K) →ₗ[K] Arr (K := K) :=
  LinearMap.id-source1Assembly.comp (HeeckLeSixQuarkQuotient.sectionLinear.comp top)

def coupling : Arr (K := K) →ₗ[K] (Fin 5 → K) :=
  couplingDecodeLinear.comp (residual.comp remainder)

def cleaned : Arr (K := K) →ₗ[K] Arr (K := K) := remainder-couplingAssembly.comp coupling

def evenCoordinates : Arr (K := K) →ₗ[K] (Fin 5 → K) := evenDecodeLinear.comp (even.comp cleaned)
def oddCoordinates : Arr (K := K) →ₗ[K] (Fin 5 → K) := oddDecodeLinear.comp (odd.comp cleaned)

def source0Coordinates : Arr (K := K) →ₗ[K] (Fin 13 → K) :=
  joinZeroLinear.comp (evenCoordinates.prod (oddCoordinates.prod (leftOfCoupling.comp coupling)))

def free (i : Fin 5) : (Fin 5 → K) →ₗ[K] K := LinearMap.proj i

def source1Coordinates : Arr (K := K) →ₗ[K] (Fin 12 → K) :=
  HeeckLeSixQuarkQuotient.sectionLinear.comp top+
    ((free 3).comp coupling).smulRight HeeckLeSixQuarkQuotient.kernelFirst+
    ((free 4).comp coupling).smulRight HeeckLeSixQuarkQuotient.kernelSecond

def decode : Arr (K := K) →ₗ[K] (Fin 25 → K) :=
  weaveLinear.comp (source0Coordinates.prod source1Coordinates)

theorem remainder_apply (c : Arr (K := K)) :
    remainder c = c-source1Assembly (HeeckLeSixQuarkQuotient.sectionMap (top c)) := rfl

theorem coupling_apply (c : Arr (K := K)) : coupling c = couplingDecode (residual (remainder c)) := rfl

theorem cleaned_apply (c : Arr (K := K)) : cleaned c = remainder c-couplingAssembly (coupling c) := rfl

theorem evenCoordinates_apply (c : Arr (K := K)) : evenCoordinates c = evenDecode (even (cleaned c)) := rfl

theorem oddCoordinates_apply (c : Arr (K := K)) : oddCoordinates c = oddDecode (odd (cleaned c)) := rfl

theorem source0Coordinates_apply (c : Arr (K := K)) : source0Coordinates c =
    joinZero (evenCoordinates c) (oddCoordinates c) (leftOfCoupling (coupling c)) := rfl

theorem source1Coordinates_apply (c : Arr (K := K)) : source1Coordinates c =
    HeeckLeSixQuarkQuotient.solve (top c) (coupling c 3) (coupling c 4) := rfl

theorem decode_apply (c : Arr (K := K)) : decode c = weave (source0Coordinates c) (source1Coordinates c) := rfl

/-- Expected values used only to state the uniform left-inverse proof. -/
def trueCoupling (v : Fin 25 → K) : Fin 5 → K :=
  ![select0 v 6,select0 v 11,select0 v 12,select1 v 8,select1 v 10]

omit [CharZero K] in
theorem trueCoupling_left (v : Fin 25 → K) : leftOfCoupling (trueCoupling v) = leftSelect (select0 v) := rfl

omit [CharZero K] in
theorem trueCoupling_3 (v : Fin 25 → K) : trueCoupling v 3 = select1 v 8 := rfl

omit [CharZero K] in
theorem trueCoupling_4 (v : Fin 25 → K) : trueCoupling v 4 = select1 v 10 := rfl

theorem remainder_assemble (v : Fin 25 → K) : remainder (assemble v) =
    evenAssembly (evenSelect (select0 v))+oddAssembly (oddSelect (select0 v))+
      couplingAssembly (trueCoupling v) := by
  have hb := congrArg source1Assembly (HeeckLeSixQuarkQuotient.solve_forward (select1 v))
  simp only [HeeckLeSixQuarkQuotient.solve, map_add, map_smul] at hb
  rw [remainder_apply, top_assemble, assemble_split, ← hb, source0_split,
    coupling_split, trueCoupling_left, trueCoupling_3, trueCoupling_4]
  abel

theorem coupling_assemble (v : Fin 25 → K) : coupling (assemble v) = trueCoupling v := by
  rw [coupling_apply, remainder_assemble]
  simp only [map_add, residual_even, residual_odd, zero_add,
    residual_coupling, couplingDecode_forward]

theorem cleaned_assemble (v : Fin 25 → K) : cleaned (assemble v) =
    evenAssembly (evenSelect (select0 v))+oddAssembly (oddSelect (select0 v)) := by
  rw [cleaned_apply, coupling_assemble, remainder_assemble]
  abel

theorem evenCoordinates_assemble (v : Fin 25 → K) : evenCoordinates (assemble v) = evenSelect (select0 v) := by
  rw [evenCoordinates_apply, cleaned_assemble, map_add, even_even, even_odd,
    add_zero, evenDecode_forward]

theorem oddCoordinates_assemble (v : Fin 25 → K) : oddCoordinates (assemble v) = oddSelect (select0 v) := by
  rw [oddCoordinates_apply, cleaned_assemble, map_add, odd_even, odd_odd,
    zero_add, oddDecode_forward]

theorem source0Coordinates_assemble (v : Fin 25 → K) : source0Coordinates (assemble v) = select0 v := by
  rw [source0Coordinates_apply, evenCoordinates_assemble, oddCoordinates_assemble,
    coupling_assemble, trueCoupling_left, join_select]

theorem source1Coordinates_assemble (v : Fin 25 → K) : source1Coordinates (assemble v) = select1 v := by
  rw [source1Coordinates_apply, top_assemble, coupling_assemble,
    trueCoupling_3, trueCoupling_4, HeeckLeSixQuarkQuotient.solve_forward]

theorem decode_assemble (v : Fin 25 → K) : decode (assemble v) = v := by
  rw [decode_apply, source0Coordinates_assemble, source1Coordinates_assemble, weave_select]

def rawAssembly : (Fin 25 → K) →ₗ[K] Arr (K := K) := combination HeeckLeSixQuarkRecipe.orbit

theorem normalized_rawAssembly (v : Fin 25 → K) :
    HeeckLeSixQuarkBlocks.normalize (LiSixQuarkReducedAction.extraction (rawAssembly v)) = assemble v := by
  change HeeckLeSixQuarkBlocks.normalize
    (LiSixQuarkReducedAction.extraction (∑ j : Fin 25, v j • HeeckLeSixQuarkRecipe.orbit j)) = _
  rw [map_sum, map_sum]
  simp only [map_smul, HeeckLeSixQuarkRecipe.extraction_orbit,
    HeeckLeSixQuarkBlocks.normalize_orbit]
  unfold assemble combination
  rfl

def extraction : Arr (K := K) →ₗ[K] (Fin 25 → K) :=
  decode.comp (HeeckLeSixQuarkBlocks.normalize.comp LiSixQuarkReducedAction.extraction)

theorem extraction_rawAssembly (v : Fin 25 → K) : extraction (rawAssembly v) = v := by
  change decode (HeeckLeSixQuarkBlocks.normalize (LiSixQuarkReducedAction.extraction (rawAssembly v))) = v
  rw [normalized_rawAssembly, decode_assemble]

end
end GUT.HeeckLeSixQuarkExtraction
