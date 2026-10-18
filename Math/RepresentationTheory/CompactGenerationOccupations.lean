import Math.RepresentationTheory.GenerationTensorSupport

namespace Math.CompactGenerationOccupations
set_option autoImplicit false
open scoped BigOperators

def triples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range (n+1)).flatMap fun a =>
    (List.range (n-a+1)).map fun b => (a,b,n-a-b)

theorem mem_triples (n a b c : Nat) : (a,b,c) ∈ triples n ↔ a+b+c=n := by
  simp only [triples, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨x,hx,y,hy,h1,h2,h3⟩
    omega
  · intro h
    exact ⟨a,by omega,b,by omega,rfl,rfl,by omega⟩


def contiguous (a b c : Nat) : Fin (a+(b+c)) → Fin 3 :=
  Fin.append (fun _ : Fin a => 0)
    (Fin.append (fun _ : Fin b => 1) (fun _ : Fin c => 2))

theorem contiguous_counts (a b c : Nat) (s : Fin 3) :
    (FiniteExteriorExhaustion.counts (a+(b+c)) (contiguous a b c) s).val =
      if s=0 then a else if s=1 then b else c := by
  change (Finset.univ.filter (fun i => contiguous a b c i=s)).card = _
  rw [show (Finset.univ.filter (fun i => contiguous a b c i=s)).card =
      ∑ i, if contiguous a b c i=s then (1 : Nat) else 0 from by simp]
  rw [Fin.sum_univ_add]
  simp only [contiguous, Fin.append_left, Fin.append_right]
  rw [Fin.sum_univ_add]
  fin_cases s <;> simp [Fin.append_left, Fin.append_right]

theorem counts_cast {n m : Nat} (h : n=m) (p : Fin n → Fin 3) (s : Fin 3) :
    (FiniteExteriorExhaustion.counts m (fun i => p (i.cast h.symm)) s).val =
      (FiniteExteriorExhaustion.counts n p s).val := by
  subst m
  rfl

theorem attainable_iff (n : Nat) (v : Fin 3 → Fin (n+1)) :
    v ∈ Set.range (FiniteExteriorExhaustion.counts (S := Fin 3) n) ↔
      ∑ s, (v s).val = n := by
  constructor
  · intro hv
    exact FiniteExteriorExhaustion.occupation_sum n ⟨v,hv⟩
  · intro hv
    let a := (v 0).val
    let b := (v 1).val
    let c := (v 2).val
    have hn : a+(b+c)=n := by
      simpa [a,b,c,Fin.sum_univ_succ] using hv
    refine ⟨(fun i => contiguous a b c (i.cast hn.symm)), ?_⟩
    funext s
    apply Fin.ext
    rw [counts_cast hn, contiguous_counts]
    fin_cases s <;> simp [a,b,c]

/-- A bounded count vector, realized by a contiguous generation word. -/
def fromTriple (n : ℕ) (t : ℕ × ℕ × ℕ) (h : t.1+t.2.1+t.2.2=n) :
    GenerationTensorSupport.Occupation n :=
  ⟨fun s => ⟨if s=0 then t.1 else if s=1 then t.2.1 else t.2.2, by
      split_ifs <;> omega⟩,
    (attainable_iff n _).mpr (by simp [Fin.sum_univ_succ]; omega)⟩

/-- Dependent triangular index: distinct count pairs require no deduplication. -/
abbrev Index (n : ℕ) := Σ a : Fin (n+1), Fin (n-a.val+1)

def toOccupation (n : ℕ) (i : Index n) : GenerationTensorSupport.Occupation n :=
  fromTriple n (i.1.val,i.2.val,n-i.1.val-i.2.val) (by
    change i.1.val+i.2.val+(n-i.1.val-i.2.val)=n
    have := i.1.isLt
    have := i.2.isLt
    omega)

def fromOccupation (n : ℕ) (o : GenerationTensorSupport.Occupation n) : Index n :=
  ⟨o.val 0, ⟨(o.val 1).val,by
    have h := FiniteExteriorExhaustion.occupation_sum n o
    simp [Fin.sum_univ_succ] at h
    omega⟩⟩

def equiv (n : ℕ) : Index n ≃ GenerationTensorSupport.Occupation n where
  toFun := toOccupation n
  invFun := fromOccupation n
  left_inv i := by
    rcases i with ⟨a,b⟩
    rfl
  right_inv o := by
    apply Subtype.ext
    funext s
    apply Fin.ext
    have h := FiniteExteriorExhaustion.occupation_sum n o
    simp [Fin.sum_univ_succ] at h
    fin_cases s
    · rfl
    · rfl
    · simp [toOccupation,fromOccupation,fromTriple]
      omega

/-- Explicit alternative, deliberately not a global instance. -/
@[instance_reducible]
def fintype (n : ℕ) : Fintype (GenerationTensorSupport.Occupation n) :=
  Fintype.ofEquiv (Index n) (equiv n)

/-- Every leaf explicitly selects the compact occupation enumeration. -/
@[instance_reducible]
def choiceFintype {G : Type*} [Group G] :
    (t : ExteriorContentTree.Content G) → Fintype (GenerationTensorSupport.Choice t)
  | .leaf a => fintype a.degree
  | .node l r =>
    letI := choiceFintype l
    letI := choiceFintype r
    inferInstanceAs (Fintype (GenerationTensorSupport.Choice l × GenerationTensorSupport.Choice r))

end Math.CompactGenerationOccupations
